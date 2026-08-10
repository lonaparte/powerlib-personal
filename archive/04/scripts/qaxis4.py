"""Where does the regulating branch lose stability, and to WHICH mode?

The tracked critical mode is damped hard by a regulating droop
(d alpha/d k_q = -55.8), but the loop also creates its own mode.  Whichever
of the two is least damped sets the margin, so the branch has to be scanned
with ALL modes visible, not with the tracked one only.
"""
import math, time
import numpy as np, sympy as sp
from scipy.linalg import eig
from scipy.optimize import brentq
exec(open('selfhead.py').read())
_qsrc = open('qaxis.py').read()
exec(_qsrc.split('# ---------------------------------------------------'
                 '-------------- models')[1].split('M6 = build')[0])
LOG = open('sweep20/qaxis4.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()
M8A = build('M8A'); M8B = build('M8B')
prb = gset('G1')
Ps = 3*prb['V']**2/(4*prb['Xg'])
grid = np.linspace(0.05, 0.985, 60)*Ps
va = []
for P in grid:
    qd = dict(prb, P=P); xx = equil(qd)
    cm = crit_mode(jac(xx, qd)) if xx is not None else None
    va.append(None if cm is None else cm.real)
for a_, b_, fa, fb in zip(grid[:-1], grid[1:], va[:-1], va[1:]):
    if fa is not None and fb is not None and fa < 0 <= fb:
        lo, hi = a_, b_
        for _ in range(45):
            mm = 0.5*(lo+hi); qd = dict(prb, P=mm); xx = equil(qd)
            cm = crit_mode(jac(xx, qd)) if xx is not None else None
            if cm is None or cm.real >= 0: hi = mm
            else: lo = mm
        PH = 0.5*(lo+hi); break
P0 = margin_point(prb, PH, 0.10)
st4 = equil(dict(prb, P=P0)); w0ref = nf_coeffs(dict(prb, P=P0))['w0']
pr0 = dict(prb, P=P0, zc=0.707, wc=100.*w0ref, kq=0.0, Vref=0.0)
s8 = lift(M8A, st4, pr0)
Vref0 = math.hypot(pr0['V']*math.cos(s8[0]) - pr0['Xg']*s8[6],
                   -pr0['V']*math.sin(s8[0]) + pr0['Xg']*s8[4])
prk = dict(pr0, Vref=Vref0)
A0 = jacn(M8B, lift(M8B, st4, dict(prk, kq=0.0)), dict(prk, kq=0.0))
ev0, _, VR0 = eig(A0, left=True, right=True)
k0 = max((i for i in range(8) if ev0[i].imag > 1e-9), key=lambda i: ev0[i].real)
q0 = VR0[:, k0]/np.linalg.norm(VR0[:, k0])

def modes(kq):
    prq = dict(prk, kq=kq)
    A = jacn(M8B, lift(M8B, st4, prq), prq)
    e, _, VR = eig(A, left=True, right=True)
    ov = [abs(np.vdot(q0, VR[:, i]/np.linalg.norm(VR[:, i]))) for i in range(8)]
    j = int(np.argmax(ov))
    cxm = [i for i in range(8) if e[i].imag > 1e-9]
    km = max(cxm, key=lambda i: e[i].real)
    return e[j], ov[j], e[km], km == j

out("  regulating branch (k_q<0):  tracked = continuation of the open-loop")
out("  critical mode; worst = whichever mode is least damped")
out("   k_q     tracked alpha  overlap   worst alpha   worst w0   same?")
for kq in (0.0, -0.01, -0.05, -0.1, -0.12, -0.15, -0.18, -0.2, -0.3, -0.5):
    lt, ov, lw, same = modes(kq)
    out(f"  {kq:+.3f}  {-lt.real:+.6f}   {ov:.4f}   {-lw.real:+.6f}  "
        f"{lw.imag:9.4f}   {same}")
def gw(kq):
    return modes(kq)[2].real
lo, hi = -0.01, -0.5
try:
    kc = brentq(gw, lo, hi, xtol=1e-12)
    lt, ov, lw, same = modes(kc)
    out(f"  regulating-side stability limit: k_q = {kc:+.6f}, "
        f"w = {lw.imag:.4f}, tracked-mode overlap {ov:.4f}, is-tracked {same}")
except Exception as e:
    out(f"  no crossing bracketed on [-0.01,-0.5]: {e}")
a0 = -ev0[k0].real
out(f"  anti-regulating side (k_q>0): alpha_0/|d alpha/d k_q| = "
    f"{a0/55.829161:.6f} predicted; measured:")
def gp(kq):
    return -modes(kq)[2].real
try:
    kp = brentq(lambda k: modes(k)[2].real, 1e-5, 0.05, xtol=1e-14)
    out(f"  k_q,crit(+) = {kp:.6f}   ratio to prediction "
        f"{kp/(a0/55.829161):.4f}")
except Exception as e:
    out(f"  bracket failed: {e}")
out(f"DONE wall={time.time()-T0:.0f}s")
