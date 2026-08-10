"""Two consequences of the q-axis result, both of which reach back into
already-recorded numbers.

(a) The multiplicative term is not a q-axis curiosity.  A drive is
    multiplicative whenever the driven parameter MULTIPLIES a state inside
    the vector field.  In the GFL that is true of V (it multiplies sin/cos th)
    and of Q (it multiplies i_d through v_gq Q and enters v_gd), and false of
    P (it enters the DC-link balance as a pure additive term).  So P is the
    control: its additive and multiplicative c_x must agree to machine
    precision, and if they do not, the extended machinery is wrong.
    Then: does putting the missing terms in move the recorded V-channel
    threshold toward the measured one?  The recorded gap was +2.39/+3.56/
    +4.54/+5.40% over alpha=0.05..0.20 and +0.46% for idx17; those are the
    residuals this campaign has been chasing.

(b) The Q-V droop gain enters alpha with an exact first-order coefficient
    dlambda/dk_q = <p, (dA/dk_q) q>, which is a formula parameter, not a
    swept number.  Reported with the swept curve as a check, plus the gain at
    which alpha crosses zero.

Also: the GFM has no constant-i_q assumption to remove in the first place --
its i_q is algebraic in (delta, Q_f) in the 4-state and a genuinely coupled
state in the 6-state.  Shown by evaluating d i_q/d(states), not asserted.
"""
import math, time
import numpy as np
import sympy as sp
from scipy.linalg import eig

exec(open('selfhead.py').read())
_src4 = open('mech4.py').read().split('CELLS = ')[0]
_ns = {}
exec(compile(_src4.replace("LOG = open('sweep20/mech4.log', 'w')",
                           "LOG = open('/dev/null','w')"), 'm4', 'exec'), _ns)
cx_hand = _ns['cx_hand']; hopf = _ns['hopf']
two_carrier_nf = _ns['two_carrier_nf']; guard_root = _ns['guard_root']

_qsrc = open('qaxis.py').read()
exec(_qsrc.split('# ---------------------------------------------------'
                 '-------------- models')[1].split('M6 = build')[0])

LOG = open('sweep20/qaxis3.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

# ------------------------------------------------ extended 4-state tensors
X4 = (th_, xp_, Vdc_, xi_)
DRV = {'V': V_, 'P': P_, 'Q': Q_}
EXT = {}
for kdr, sdr in DRV.items():
    XEx = X4 + (sdr,)
    d1 = sp.derive_by_array(list(f_), XEx)
    d2 = sp.derive_by_array(d1, XEx)
    d3 = sp.derive_by_array(d2, XEx)
    EXT[kdr] = (sp.lambdify(_args, d2, 'numpy'), sp.lambdify(_args, d3, 'numpy'))
out(f"extended 4-state tensors built [{time.time()-T0:.0f}s]")


def cx4(kdr, A, st, pr, q, p, w0, wp, fu, mult=True):
    a = _avl(st, pr)
    Hm = np.array(EXT[kdr][0](*a), float)
    Tm = np.array(EXT[kdr][1](*a), float)
    if not mult:                      # zero every entry touching the drive
        Hm = Hm.copy(); Tm = Tm.copy()
        Hm[4, :, :] = 0; Hm[:, 4, :] = 0
        Tm[4, :, :, :] = 0; Tm[:, 4, :, :] = 0; Tm[:, :, 4, :] = 0
    Bt = lambda u, v: np.einsum('kji,j,k->i', Hm, u, v)
    Ct = lambda u, v, w: np.einsum('lkji,j,k,l->i', Tm, u, v, w)
    ext = lambda v, last: np.concatenate([v, [last]])
    I = np.eye(4)
    Hv = np.linalg.solve(1j*wp*I - A, fu.astype(complex)); Hc = np.conj(Hv)
    qt = ext(q, 0.0); Ht = ext(Hv, 1.0); Hct = ext(Hc, 1.0)
    gp = np.linalg.solve(1j*(w0+wp)*I - A, Bt(qt, Ht))
    gm = np.linalg.solve(1j*(w0-wp)*I - A, Bt(qt, Hct))
    d0 = -np.linalg.solve(A, Bt(Ht, Hct))
    return (np.vdot(p, Ct(qt, Ht, Hct)) + np.vdot(p, Bt(Ht, ext(gm, 0.))) +
            np.vdot(p, Bt(Hct, ext(gp, 0.))) + np.vdot(p, Bt(qt, ext(d0, 0.))))


out("")
out("=== (a1) control: is the extended machinery consistent?")
out("    P must be purely additive (it never multiplies a state);")
out("    V and Q must not be.")
prb = gset('G1'); PH = hopf(prb)
prH = dict(prb, P=PH); stH = equil(prH); coH = nf_coeffs(prH)
AH = jac(stH, prH); w0H = coH['w0']; qH = coH['q']; pH = coH['p']
hs = 1e-6
out("    channel   c_x additive        c_x multiplicative   rel. change")
for kdr, key in (('V', 'V'), ('P', 'P'), ('Q', 'Q')):
    fu = (rhs(stH, dict(prH, **{key: prH[key]+hs}))
          - rhs(stH, dict(prH, **{key: prH[key]-hs})))/(2*hs)
    wp = 0.9*w0H
    ca = cx4(kdr, AH, stH, prH, qH, pH, w0H, wp, fu, mult=False)
    cm = cx4(kdr, AH, stH, prH, qH, pH, w0H, wp, fu, mult=True)
    chk = cx_hand(AH, stH, prH, qH, pH, w0H, wp, fu)
    out(f"      {kdr}      {ca.real:+.7e}  {cm.real:+.7e}  "
        f"{cm.real/ca.real-1:+.3e}   (old machinery {chk.real:+.7e}, "
        f"reldiff {abs(ca/chk-1):.1e})")

out("")
out("=== (a2) does the multiplicative term close the recorded V-channel gap?")
out("    recorded (mech4.log): measured vs 3rd order, c_x from the Hopf point")
CELL = [('G1 V r=0.9', {}, 0.9, 'V',
         [(0.05, 8.433762e-05, 8.635201e-05), (0.10, 1.186533e-04, 1.228787e-04),
          (0.15, 1.446188e-04, 1.511781e-04), (0.20, 1.662438e-04, 1.752172e-04)]),
        ('idx17 r=0.92', dict(kp=55., ki=1200., Xg=0.40), 0.92, 'V',
         [(0.08, 7.099020e-03, 7.131990e-03)])]
for tag, over, rat, kdr, rows in CELL:
    prb2 = gset('G1', **over); PH2 = hopf(prb2)
    prH2 = dict(prb2, P=PH2); stH2 = equil(prH2); coH2 = nf_coeffs(prH2)
    AH2 = jac(stH2, prH2); w02 = coH2['w0']; wp2 = rat*w02
    fuH = (rhs(stH2, dict(prH2, V=prH2['V']+hs))
           - rhs(stH2, dict(prH2, V=prH2['V']-hs)))/(2*hs)
    R = two_carrier_nf(prH2, wp2, fuH)
    cxa = cx4(kdr, AH2, stH2, prH2, coH2['q'], coH2['p'], w02, wp2,
              fuH, mult=False).real
    cxm = cx4(kdr, AH2, stH2, prH2, coH2['q'], coH2['p'], w02, wp2,
              fuH, mult=True).real
    c1r = R['c1'].real
    hh2 = R['h']
    pH2c = np.vdot(R['p'], hh2[(0, 0, 2, 0)])
    pH11 = np.vdot(R['p'], hh2[(0, 0, 1, 1)])
    pH02 = np.vdot(R['p'], hh2[(0, 0, 0, 2)])
    out(f"  {tag}: c_x add {cxa:+.6e}  mult {cxm:+.6e}  "
        f"({cxm/cxa-1:+.3%})")
    out("    alpha   measured      3rd(add)     err     3rd(mult)    err")
    for marg, emeas, e3rec in rows:
        P0 = margin_point(prb2, PH2, marg)
        pr = dict(prb2, P=P0); co = nf_coeffs(pr)
        st = co['st']; w0 = co['w0']; alpha = co['alpha']; lamO = co['lam']
        wp = rat*w0
        fV = (rhs(st, dict(pr, V=pr['V']+hs))
              - rhs(st, dict(pr, V=pr['V']-hs)))/(2*hs)
        F = np.vdot(co['p'], fV)
        J = abs(lamO)*abs(F)/abs(wp**2 + lamO**2)

        def kick(eps):
            a = 0.5*eps
            return abs(eps*J + a*a*(pH2c + pH11 + pH02))

        def thr(cxr):
            lo, hi = 1e-9, 6*math.sqrt(alpha/c1r)/J
            for _ in range(200):
                mm = 0.5*(lo+hi)
                aeff = alpha - cxr*0.25*mm*mm
                g = kick(mm) - guard_root(aeff, c1r, 0.0)
                if not (g == g) or g > 0: hi = mm
                else: lo = mm
            return 0.5*(lo+hi)
        ea = thr(cxa); em = thr(cxm)
        out(f"    {marg:.2f}   {emeas:.6e}  {ea:.6e} {(ea-emeas)/emeas*100:+6.2f}%"
            f"  {em:.6e} {(em-emeas)/emeas*100:+6.2f}%   "
            f"(recorded {e3rec:.6e})")

out("")
out("=== (b) Q-V droop: exact first-order coefficient of alpha in k_q")
M8B = build('M8B'); M8A = build('M8A')
Ps = 3*prb['V']**2/(4*prb['Xg'])
P0 = margin_point(prb, PH, 0.10)
st4 = equil(dict(prb, P=P0))
co4 = nf_coeffs(dict(prb, P=P0)); w0ref = co4['w0']
pr0 = dict(prb, P=P0, zc=0.707, wc=100.*w0ref, kq=0.0, Vref=0.0)
st8 = lift(M8A, st4, pr0)
vgd0 = pr0['V']*math.cos(st8[0]) - pr0['Xg']*st8[6]
vgq0 = -pr0['V']*math.sin(st8[0]) + pr0['Xg']*st8[4]
Vref0 = math.hypot(vgd0, vgq0)
dVdiq = -pr0['Xg']*vgd0/Vref0
out(f"    d|v_pcc|/d i_q = {dVdiq:+.6f} < 0  =>  negative feedback needs "
    f"k_q*d|v|/di_q > 0, i.e. k_q < 0")
prk = dict(pr0, kq=0.0, Vref=Vref0)
stk = lift(M8B, st4, prk)
A0 = jacn(M8B, stk, prk)
ev, VL, VR = eig(A0, left=True, right=True)
kk = max((i for i in range(8) if ev[i].imag > 1e-9), key=lambda i: ev[i].real)
lam0 = ev[kk]; q0 = VR[:, kk]; q0 = q0/q0[0]
p0 = VL[:, kk]; p0 = p0/np.vdot(q0, p0)
hk = 1e-5
dA = (jacn(M8B, stk, dict(prk, kq=hk)) - jacn(M8B, stk, dict(prk, kq=-hk)))/(2*hk)
dlam = np.vdot(p0, dA @ q0)
out(f"    lambda(0) = {lam0:.6f}")
out(f"    dlambda/dk_q = <p, (dA/dk_q) q> = {dlam:.6f}")
out(f"    => d alpha/d k_q = {-dlam.real:+.6f}   "
    f"(alpha_0 = {-lam0.real:.6f}, so alpha doubles at "
    f"|k_q| = {abs(lam0.real/dlam.real):.5f})")
out(f"    d w0/d k_q   = {dlam.imag:+.6f}")
out("    check against a direct sweep (mode tracked by eigenvector overlap):")
out("    k_q       alpha        linear pred    w0       overlap")
for kq in (-0.002, -0.005, -0.01, -0.02, -0.05, -0.1):
    prq = dict(prk, kq=kq)
    Aq = jacn(M8B, lift(M8B, st4, prq), prq)
    evq, _, VRq = eig(Aq, left=True, right=True)
    ov = [abs(np.vdot(q0/np.linalg.norm(q0), VRq[:, i]/np.linalg.norm(VRq[:, i])))
          for i in range(8)]
    j = int(np.argmax(ov))
    pred = -lam0.real - dlam.real*kq
    out(f"    {kq:+.3f}  {-evq[j].real:+.7f}  {pred:+.7f}  "
        f"{evq[j].imag:8.4f}  {ov[j]:.4f}")

out("")
out("=== (c) the GFM never froze i_q")
import gfmlib as G
d_, om_, Pf_, Qf_ = sp.symbols('d om Pf Qf', real=True)
Pref_, Qref_, Vs_, Xgs_, Ms_, Ds_, mqs_, wcs_ = sp.symbols(
    'Pref Qref V Xg M D mq wc', real=True)
Eg = 1 - mqs_*(Qf_ - Qref_)
iq_alg = (Vs_*sp.cos(d_) - Eg)/Xgs_
out(f"    4-state:  i_q = {iq_alg}")
out(f"      d i_q/d delta = {sp.simplify(sp.diff(iq_alg, d_))}")
out(f"      d i_q/d Q_f   = {sp.simplify(sp.diff(iq_alg, Qf_))}")
out("      -> i_q is a FUNCTION OF TWO STATES, never a parameter;")
out("         the q axis is dynamic in the 4-state already.")
out("    6-state (current loop): d i_q/dt = w_cur((V cos d - E)/Xg - i_q)")
out("      depends on delta and Q_f -> no block triangularity at all,")
out("      i.e. the GFM has no 6-vs-8 choice to make.")
out(f"DONE wall={time.time()-T0:.0f}s")
