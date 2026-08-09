"""Is one channel obtainable from another by a linear rescaling?

The kick coefficient J is linear in f_u, so if the erosion coefficient
were also proportional to |<p,f_u>|^2 the whole threshold would scale as
1/|<p,f_u>| and one channel would indeed determine all of them.  But
Re c_x is a quadratic form in the FULL response vector H = (i w_p I -
A)^{-1} f_u -- through the sum-frequency, difference-frequency and DC
second-order solutions -- not in its modal projection alone.  Whether the
proportionality holds is therefore a property of the device, not a
theorem, and it is decided here by direct evaluation (no simulation).

Printed per channel and per frequency ratio: the modal coupling
|<p,f_u>|, the kick coefficient J, Re c_x, the ratio Re c_x/|<p,f_u>|^2
(constant across channels iff the linear-rescaling picture holds), and
the closed-form threshold.  Channel ratios are then compared against the
inverse coupling ratio, which is what a purely linear map would predict.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/chanlin.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
_src = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src.replace("LOG = open('sweep20/mech4.log', 'w')",
                          "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']
prb = gset('G1'); PH = hopf(prb)
P0 = margin_point(prb, PH, 0.10)
pr = dict(prb, P=P0); co = nf_coeffs(pr)
st = co['st']; w0 = co['w0']; alpha = co['alpha']
lam = co['lam']; pv = co['p']; qv = co['q']; c1 = co['c1']
A = jac(st, pr); hs = 1e-6
FU = {}
for k, key in (('V', 'V'), ('P', 'P'), ('Q', 'Q')):
    FU[k] = (rhs(st, dict(pr, **{key: pr[key]+hs}))
             - rhs(st, dict(pr, **{key: pr[key]-hs})))/(2*hs)
out(f"G1 margin 0.10, alpha={alpha:.4f}, Re c1={c1.real:.5e}")
out(" r     ch  |<p,f_u>|    J           Re c_x        "
    "Re c_x/|<p,f_u>|^2   eps_c(closed)")
tab = {}
for r in (0.60, 0.75, 0.90, 1.00, 1.15):
    wp = r*w0
    tab[r] = {}
    for k in ('V', 'P', 'Q'):
        fu = FU[k]
        F = abs(np.vdot(pv, fu))
        J = abs(lam)*F/abs(wp**2 + lam**2)
        cx = cx_hand(A, st, pr, qv, pv, w0, wp, fu).real
        lo, hi = 1e-14, 1.0
        for _ in range(200):
            m = 0.5*(lo+hi); a2 = 0.25*m*m
            aeff = alpha - cx*a2
            rgv = math.sqrt(aeff/c1.real) if aeff > 0 else -1.0
            if rgv < 0 or m*J > rgv: hi = m
            else: lo = m
        ec = 0.5*(lo+hi)
        tab[r][k] = (F, J, cx, ec)
        out(f"{r:.2f}   {k}   {F:9.3f}  {J:.5e}  {cx:+.5e}  "
            f"{cx/F**2:+.5e}   {ec:.5e}")
out("")
out("channel ratios (V as reference):")
out(" r     eps_c ratio P/V   Q/V   |  inverse coupling ratio P/V   Q/V")
for r in tab:
    eV, eP, eQ = tab[r]['V'][3], tab[r]['P'][3], tab[r]['Q'][3]
    FV, FP, FQ = tab[r]['V'][0], tab[r]['P'][0], tab[r]['Q'][0]
    out(f"{r:.2f}       {eP/eV:.4f}  {eQ/eV:.4f}   |        "
        f"{FV/FP:.4f}  {FV/FQ:.4f}")
out("")
out("Re c_x/|<p,f_u>|^2 spread across channels at each r "
    "(1.000 = exact linear rescaling):")
for r in tab:
    v = [tab[r][k][2]/tab[r][k][0]**2 for k in ('V', 'P', 'Q')]
    out(f"{r:.2f}   V {v[0]/v[0]:.4f}   P {v[1]/v[0]:.4f}   Q {v[2]/v[0]:.4f}")
out("DONE")
