"""Why amplitude(Vdc)-dominated modes are weakly subcritical: decompose
c1's cubic-projection term by the number of theta indices in the tensor
contraction. GFL's strong nonlinearity is trigonometric (theta channel);
a Vdc-dominated eigenvector suppresses the 3-theta block ~ |q_th|^3.
Also: kappa=2a quintic scaling check on a second set (Xg=0.70, three
margins). Budget ~4 min.
"""
exec(open('selfhead.py').read())
import time
LOG = open('sweep20/c1decomp.log', 'w')
def out(m):
    LOG.write(m + '\n'); LOG.flush()
T0 = time.time()

def build(over, marg):
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
    return dict(prb, P=P)

SETS = [
    ('G1 (strong)',        {},                     0.10),
    ('Xg=0.70 (strong)',   dict(Xg=0.70),          0.10),
    ('mix12 (strong)',     dict(kp=40., ki=800., kpv=1.5, kiv=60.,
                                C=0.015, Xg=0.45), 0.10),
    ('mix16 (strong)',     dict(kp=45., ki=900., Xg=0.55), 0.10),
    ('Q=+0.15 (strong)',   dict(Q=0.15),           0.10),
    ('C=0.02 (strong)',    dict(C=0.02),           0.10),
    ('Xg=0.35 (weak)',     dict(Xg=0.35),          0.10),
    ('kp30ki600 (weak)',   dict(kp=30., ki=600.),  0.10),
    ('C=0.005 (weak)',     dict(C=0.005),          0.10),
    ('Q=-0.15 (weak)',     dict(Q=-0.15),          0.10),
    ('V=1.06 (weak)',      dict(V=1.06),           0.10),
    ('mix13 (trans)',      dict(kp=65., ki=1600., kpv=0.8, kiv=35.,
                                C=0.008, Xg=0.60), 0.10),
]
out(f"{'set':>20} {'|q_th|':>7} {'Re c1':>8} | C3 by #theta-idx "
    f"(Re<p,.>/2): 3th, 2th, 1th, 0th | ReC3tot/2  ReB-terms/2")
for tag, over, marg in SETS:
    pr = build(over, marg)
    co = nf_coeffs(pr)
    st = co['st']; qv = co['q']; pv = co['p']
    a = _avl(st, pr)
    w0 = co['w0']
    A = jac(st, pr)
    grp = [0j, 0j, 0j, 0j]
    for i in range(4):
        for j in range(4):
            for k in range(4):
                for l in range(4):
                    t = _Tl[i][j][k][l](*a)
                    if t == 0:
                        continue
                    nth = (j == 0) + (k == 0) + (l == 0)
                    grp[nth] += np.conj(pv[i])*t*qv[j]*qv[k]*np.conj(qv[l])
    def B2c(u, v):
        return np.array([sum(_Hl[i][j][kk](*a)*u[j]*v[kk]
                             for j in range(4) for kk in range(4))
                         for i in range(4)])
    h11 = np.linalg.solve(A, B2c(qv, qv.conj()))
    h20 = np.linalg.solve(2j*w0*np.eye(4) - A, B2c(qv, qv))
    Bterms = (-2*np.vdot(pv, B2c(qv, h11))
              + np.vdot(pv, B2c(qv.conj(), h20)))/2
    qn = qv/np.linalg.norm(qv)
    out(f"{tag:>20} {abs(qn[0]):7.3f} {co['c1'].real:8.1f} | "
        f"{grp[3].real/2:8.1f} {grp[2].real/2:8.1f} {grp[1].real/2:8.1f} "
        f"{grp[0].real/2:8.1f} | {sum(grp).real/2:8.1f} {Bterms.real:8.1f}")

# quintic scaling of kappa on Xg=0.70 (3 margins)
out("")
out("kappa=2alpha quintic-scaling check, Xg=0.70:")
_Jl = [[sp.lambdify(_args, sp.diff(f_[i], _x[j]), 'numpy')
        for j in range(4)] for i in range(4)]
def jac_a(x, prm):
    a2 = _avl(x, prm)
    return np.array([[float(_Jl[i][j](*a2)) for j in range(4)]
                     for i in range(4)])
for marg in (0.05, 0.10, 0.20):
    pr = build(dict(Xg=0.70), marg)
    co = nf_coeffs(pr)
    st = co['st']; w0 = co['w0']; qv = co['q']; pv = co['p']
    c1v = co['c1']; alpha = co['alpha']
    zg = math.sqrt(alpha/c1v.real)
    def flow_auto(x0, T, with_var=False):
        def f(t, y):
            x = y[:4]
            if not with_var:
                return rhs(x, pr)
            Phi = y[4:].reshape(4, 4)
            return np.concatenate([rhs(x, pr), (jac_a(x, pr) @ Phi).ravel()])
        y0 = (x0 if not with_var
              else np.concatenate([x0, np.eye(4).ravel()]))
        s = solve_ivp(f, (0, T), y0, method='DOP853', rtol=1e-12,
                      atol=1e-14)
        return (s.y[:4, -1] if not with_var
                else (s.y[:4, -1], s.y[4:, -1].reshape(4, 4)))
    def cycle_newton(xs, Ts, itmax=40):
        x, T = xs.copy(), Ts
        fref = rhs(xs, pr)
        for it in range(itmax):
            xT, M = flow_auto(x, T, with_var=True)
            R = np.append(xT - x, np.dot(fref, x - xs))
            if np.max(np.abs(R)) < 1e-12:
                return x, T, M, True
            A5 = np.zeros((5, 5))
            A5[:4, :4] = M - np.eye(4)
            A5[:4, 4] = rhs(xT, pr)
            A5[4, :4] = fref
            dy = np.linalg.solve(A5, -R)
            n = np.linalg.norm(dy[:4])
            cap = max(0.01, 0.5*zg)
            if n > cap:
                dy *= cap/n
            if abs(dy[4]) > 0.1*T:
                dy *= 0.1*T/abs(dy[4])
            x = x + dy[:4]; T = T + dy[4]
        return x, T, M, np.max(np.abs(R)) < 1e-9
    got = False
    for fac in (1.0, 0.85, 0.7, 1.2):
        xs = st + 2*np.real(fac*zg*qv)
        Ts = 2*math.pi/(w0 + c1v.imag*(fac*zg)**2)
        x0c, Tc, Mc, okc = cycle_newton(xs, Ts)
        if okc and abs(np.vdot(pv, x0c - st)) > 0.2*zg:
            got = True; break
    if not got:
        out(f"  marg={marg}: cycle Newton failed"); continue
    kap = math.log(max(abs(m) for m in np.linalg.eigvals(Mc)))/Tc
    out(f"  marg={marg}: kappa={kap:.5f} 2a={2*alpha:.5f} "
        f"err={(kap-2*alpha)/(2*alpha)*100:+.2f}%")
out(f"DONE wall={time.time()-T0:.0f}s")
