"""Wide-parameter validation of the velocity-kick escape derivation:
   1/2 M dw_esc^2 = dU + W   (W: self-consistent climb quadrature)
Test matrix spans: near-Hopf and no-Hopf configs, fast/slow filter,
tiny/huge damping, strong droop, off-nominal V and Qref.
For each case: bisect full-4-state threshold, compare ladder rungs.
"""
import math, numpy as np
from scipy.integrate import quad, solve_ivp
from gfmlib import (mset, fold, equil, jac, crit_mode, P_of, simulate,
                    escape_event)

def Kqs(dd, pr, h=1e-6):
    return (P_of(dd+h, pr) - P_of(dd-h, pr))/(2*h)

def run_case(tag, pr):
    df, Pm = fold(pr)
    if pr['Pref'] >= 0.98*Pm:
        print(f"{tag:26s}  P too close to fold"); return
    st = equil(pr)
    if st is None:
        print(f"{tag:26s}  no equilibrium"); return
    lam = crit_mode(jac(st, pr))
    if lam is not None and lam.real >= 0:
        print(f"{tag:26s}  unstable (in Hopf window), skip"); return
    ss = equil(pr, branch='saddle')
    M, D, wc = pr['M'], pr['D'], pr['wc']
    dstar, dsad = st[0], ss[0]
    dU, _ = quad(lambda x: P_of(x, pr) - pr['Pref'], dstar, dsad, limit=200)
    w_sw = math.sqrt(max(Kqs(dstar, pr), 1e-6)/M)
    T = min(120, max(20, 40*2*math.pi/w_sw))
    ev, _ = escape_event(pr)
    def escw(dw):
        x0 = st.copy(); x0[1] += dw
        s = simulate(pr, x0, T, events=ev, rtol=1e-9)
        return len(s.t_events[0]) > 0
    dw0 = math.sqrt(2*dU/M)
    lo, hi = 0.0, None
    e = 0.5*dw0
    while e < 6*dw0:
        if escw(e): hi = e; break
        lo = e; e *= 1.3
    if hi is None:
        print(f"{tag:26s}  no escape up to 6x cons."); return
    for _ in range(12):
        m = 0.5*(lo+hi)
        if escw(m): hi = m
        else: lo = m
    dwm = 0.5*(lo+hi)
    # ladder rung 3: self-consistent quadrature
    def W_climb(E):
        v0 = math.sqrt(2*E/M)
        def rhs(t, y):
            dd, v, Pf = y
            return [v, -(P_of(dd, pr) - pr['Pref'])/M, wc*(P_of(dd, pr) - Pf)]
        def hit(t, y): return y[0] - (dsad - 1e-3)
        hit.terminal = True; hit.direction = 1
        s = solve_ivp(rhs, (0, 100), [dstar, v0, pr['Pref']], method='DOP853',
                      rtol=1e-11, atol=1e-13, events=hit, dense_output=True,
                      max_step=0.005)
        if len(s.t_events[0]) == 0:
            return None
        ts = np.linspace(0, s.t_events[0][0], 6000)
        Y = np.array([s.sol(t) for t in ts])
        dd, v, Pf = Y[:, 0], Y[:, 1], Y[:, 2]
        Pof = np.array([P_of(x, pr) for x in dd])
        return np.trapezoid(D*v*v - v*(Pof - Pf), ts)
    E = dU
    ok = True
    for _ in range(6):
        W = W_climb(E)
        if W is None:
            ok = False; break
        Enew = dU + W
        if Enew <= 0:
            ok = False; break
        E = Enew
    if not ok:
        print(f"{tag:26s}  quadrature failed"); return
    dwp = math.sqrt(2*E/M)
    mg = f"{lam.real:+.3f}" if lam is not None else "  real"
    print(f"{tag:26s}  Re={mg}  dw_meas={dwm:8.4f}  cons:{100*(dw0-dwm)/dwm:+6.1f}%  "
          f"+W:{100*(dwp-dwm)/dwm:+6.1f}%   W/dU={W/dU:+6.3f}", flush=True)

print("case                        margin    threshold      rung1     rung3")
# M2 reference (already known) - one row as anchor
run_case("M2 Xg=.05 P=1.05PH", dict(mset('M2', Xg=0.05), Pref=1.05*9.1976))
# M1: supercritical rep, stable side, three loads
for P in (2.0, 4.0, 6.0):
    run_case(f"M1 Xg=.1  P={P}", dict(mset('M1', Xg=0.1), Pref=P))
# M3: fast filter, tiny D -> near-zero drain predicted
for P in (9.0, 10.5):
    run_case(f"M3 Xg=.05 P={P}", dict(mset('M3', Xg=0.05), Pref=P))
# M4: slow filter, huge D, NO Hopf window anywhere -> big drain predicted
for P in (3.0, 5.0, 6.5):
    run_case(f"M4 Xg=.1  P={P}", dict(mset('M4', Xg=0.1), Pref=P))
# M5 weak-ish grid
for P in (1.8, 2.3):
    run_case(f"M5 Xg=.3  P={P}", dict(mset('M5', Xg=0.3), Pref=P))
# strong droop
for P in (2.0, 4.5):
    run_case(f"M1 Xg=.1 mq=.3 P={P}", dict(mset('M1', Xg=0.1, mq=0.3), Pref=P))
# off-nominal V and Qref
run_case("M1 Xg=.1 V=1.1 P=4", dict(mset('M1', Xg=0.1, V=1.1), Pref=4.0))
run_case("M1 Xg=.1 Qr=.15 P=4", dict(mset('M1', Xg=0.1, Qref=0.15), Pref=4.0))
run_case("M2 Xg=.05 V=.95 P=10", dict(mset('M2', Xg=0.05, V=0.95), Pref=10.0))
print("DONE", flush=True)
