"""A4 continued: window bias on the cells where it was never measured.

Resumed after a container restart took the first run down mid-sweep.  What
it had already established, and what is not repeated here:

  A3   all five VSM cells are analytically supercritical, and the measured
       slope of D(rho) agrees in sign for all five.  The earlier "M4 has a
       negative slope" was a conditioning artefact -- alpha = 1.963 with
       w0 = 12.776 means the amplitude falls 20x across the fit window, so
       the regression had no lever arm.  Sharpened separately in wrapA3b.
  A4a  the omega_g slow cell is exactly window-converged: a_c = 0.9427847
       at 40, 80, 160, 320 and 640 drive periods, drift 0.0000% throughout.
       So the reported a_c carries no window bias at all, and the earlier
       worry about the 40-period window there is closed.
  A4b  idx17 partial: eps_c = 7.1071014e-3 at 1000 periods,
       7.0990448e-3 at 2000 (drift -0.1134%).  Continued here to 4000 and
       8000 so the drift sequence can be seen to be geometric (in which
       case the limit is bounded by the last decrement) or not.

Still open and run here: A4b to 8000 periods, and A4c, the GFM cells, whose
window bias has never been measured at all.
"""
exec(open('selfhead.py').read())
import time
import gfmlib as G
LOG = open('sweep20/wrapA34b.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"),
             'mech4lib', 'exec'), _ns)
hopf = _ns['hopf']

# =====================================================================
# A4b: idx17 GFL cell, window convergence
# =====================================================================
out("")
out("=== A4b: idx17 (kp=55 ki=1200 Xg=0.40), margin 0.08, r=0.92")
pb17 = gset('G1', kp=55., ki=1200., Xg=0.40)
PH17 = hopf(pb17)
P17 = margin_point(pb17, PH17, 0.08)
pr17 = dict(pb17, P=P17); co17 = nf_coeffs(pr17)
st17 = co17['st']; w017 = co17['w0']; al17 = co17['alpha']
rg17 = math.sqrt(al17/co17['c1'].real)
ds17 = math.pi - 2*abs(st17[0]); Vd17 = st17[2]
wp17 = 0.92*w017; Td17 = 2*math.pi/wp17
out(f"  alpha={al17:.5f} w0={w017:.4f} r_g={rg17:.5e}")


def fate17(eps, NP):
    def f(t, x):
        return rhs(x, dict(pr17, V=pr17['V'] + eps*math.cos(wp17*t)))
    def e_th(t, x): return abs(x[0] - st17[0]) - ds17
    def e_vlo(t, x): return x[2] - 0.20*Vd17
    def e_vhi(t, x): return x[2] - 2.50*Vd17
    for e in (e_th, e_vlo, e_vhi):
        e.terminal = True
    e_th.direction = 1; e_vlo.direction = -1; e_vhi.direction = 1
    s = solve_ivp(f, (0, NP*Td17), st17.copy(), method='DOP853',
                  rtol=1e-10, atol=1e-13, events=(e_th, e_vlo, e_vhi))
    return any(len(t) > 0 for t in s.t_events) or s.status < 0


prev = None
for NP in (4000, 8000):
    elo, ehi = 3.0e-3, 1.5e-2
    n = 0
    while not fate17(ehi, NP) and n < 8:
        elo = ehi; ehi *= 1.3; n += 1
    for _ in range(17):
        em = 0.5*(elo+ehi)
        if fate17(em, NP): ehi = em
        else: elo = em
    ec = 0.5*(elo+ehi)
    dr = "" if prev is None else f"  drift {(ec-prev)/prev*100:+.4f}%"
    out(f"  NP={NP:5d}  eps_c = {ec:.7e}{dr}  [{time.time()-T0:.0f}s]")
    prev = ec

# =====================================================================
# A4c: GFM cells, window convergence
# =====================================================================
out("")
out("=== A4c: GFM cells M1/M2/M4, drive on V at r=0.9, eps_c vs window")
for nm in ('M1', 'M2', 'M4'):
    pr = G.mset(nm)
    st = G.equil(pr)
    lam = G.crit_mode(G.jac(st, pr))
    w0 = lam.imag; wp = 0.9*w0; Td = 2*math.pi/wp
    dlim = math.pi + 0.20

    def fateM(eps, NP):
        def f(t, x):
            return G.rhs(x, dict(pr, V=pr['V'] + eps*math.cos(wp*t)))
        def ev(t, x): return x[0] - dlim
        ev.terminal = True; ev.direction = 1
        s = solve_ivp(f, (0, NP*Td), st.copy(), method='DOP853',
                      rtol=1e-9, atol=1e-12, events=(ev,))
        return len(s.t_events[0]) > 0 or s.status < 0

    prev = None
    out(f"  {nm}: alpha={-lam.real:.5f} w0={w0:.4f}")
    for NP in (40, 80, 160, 320, 640):
        elo, ehi = 1e-4, 0.5
        n = 0
        while not fateM(ehi, NP) and n < 6:
            elo = ehi; ehi *= 1.4; n += 1
        if not fateM(ehi, NP):
            out(f"    NP={NP:4d}  no escape up to eps={ehi:.3e}")
            continue
        for _ in range(18):
            em = 0.5*(elo+ehi)
            if fateM(em, NP): ehi = em
            else: elo = em
        ec = 0.5*(elo+ehi)
        dr = "" if prev is None else f"  drift {(ec-prev)/prev*100:+.4f}%"
        out(f"    NP={NP:4d}  eps_c = {ec:.7e}{dr}  [{time.time()-T0:.0f}s]")
        prev = ec
out(f"DONE wall={time.time()-T0:.0f}s")
