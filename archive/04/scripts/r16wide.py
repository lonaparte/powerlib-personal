"""R16 可靠表盘的大范围仿真验证:
A: GFM f(P) 单调性 + 盲区 (10 参数组 x 3 Xg x 3 V)
B: GFL P_SN 闭式 vs 数值折叠 (宽 V x Xg 网格)
C: GFL 分表盘: 两支模态各自 f(P) 单调性 (10 增益组 x 3 Xg)
D: 时域抽查: 振铃 FFT 频率 vs 特征值频率
"""
import numpy as np, math
from scipy.optimize import fsolve, linear_sum_assignment
from scipy.integrate import solve_ivp
from gfl_operating_point_stability_sim.analysis import equilibrium_angle
import sympy as sp

# ---------- GFM 模型 ----------
delta, omega, Pf, Qf = sp.symbols('delta omega Pf Qf', real=True)
Pref_s, Qref_s, V_s, Xg_s, M_s, D_s, mq_s, wc_s, En_s = sp.symbols(
    'Pref Qref V Xg M D mq wc Enom', positive=True)
E_e = En_s - mq_s*(Qf - Qref_s)
Pe = E_e*V_s/Xg_s*sp.sin(delta); Qe = (E_e**2 - E_e*V_s*sp.cos(delta))/Xg_s
fv = sp.Matrix([omega, (Pref_s - Pf - D_s*omega)/M_s, wc_s*(Pe - Pf), wc_s*(Qe - Qf)])
xv = sp.Matrix([delta, omega, Pf, Qf]); Jv = fv.jacobian(xv)
args = (delta, omega, Pf, Qf, Pref_s, Qref_s, V_s, Xg_s, M_s, D_s, mq_s, wc_s, En_s)
f_l = sp.lambdify(args, fv, 'numpy'); J_l = sp.lambdify(args, Jv, 'numpy')

def gfm_rhs(st, d):
    return np.array(f_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                        d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float).ravel()

def gfm_equil(d):
    def res(z):
        r = gfm_rhs([z[0], 0.0, d['Pref'], z[1]], d); return [r[2], r[3]]
    for dl0 in (0.1, 0.3, 0.6, 0.9, 1.2, 1.45):
        z, info, ier, msg = fsolve(res, [dl0, 0.0], full_output=True)
        st = np.array([z[0], 0.0, d['Pref'], z[1]])
        if ier == 1 and np.max(np.abs(gfm_rhs(st, d))) < 1e-9 and 0 < z[0] < np.pi/2:
            return st
    return None

def gfm_A(d):
    st = gfm_equil(d)
    if st is None: return None, None
    return np.array(J_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                        d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float), st

def swing_mode(A):
    lam, Vr = np.linalg.eig(A); Wl = np.linalg.inv(Vr)
    best = None
    for k in range(4):
        if abs(lam[k].imag) < 1e-7: continue
        p = np.abs(Vr[:, k]*Wl[k, :]); p = p/p.sum()
        sh = p[0]+p[1]
        if sh > 0.5 and (best is None or sh > best[2]):
            best = (lam[k], abs(lam[k].imag)/2/math.pi, sh)
    return best

GFM_SETS = {
    "M1": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*31),
    "M2": dict(M=0.1, D=0.2, mq=0.05, wc=2*math.pi*10),
    "M3": dict(M=0.005, D=0.02, mq=0.2, wc=2*math.pi*100),
    "M4": dict(M=0.05, D=0.5, mq=0.1, wc=2*math.pi*5),
    "M5": dict(M=0.02, D=0.02, mq=0.1, wc=2*math.pi*20),
    "M6": dict(M=0.02, D=0.05, mq=0.0, wc=2*math.pi*31),
    "M7": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*200),
    "M8": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*3),
    "M9": dict(M=0.5, D=1.0, mq=0.05, wc=2*math.pi*31),
    "M10": dict(M=0.002, D=0.1, mq=0.1, wc=2*math.pi*50),
}

print("== A: GFM f(P) 单调性 + 盲区 ==")
mono_ok = 0; mono_bad = 0; badex = []
blind = []
for name, ps in GFM_SETS.items():
    for Xgv in (0.2, 0.5, 1.0):
        for Vv in (0.8, 1.0, 1.2):
            # 数值折叠: 对 Pref 二分平衡存在性
            lo, hi = 0.01, 2.5*Vv/Xgv
            for _ in range(40):
                mid = 0.5*(lo+hi)
                d = dict(ps, Pref=mid, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)
                if gfm_equil(d) is None: hi = mid
                else: lo = mid
            pfold = lo
            fs = []; last_osc = None
            grid = np.linspace(0.05*pfold, 0.999*pfold, 120)
            for P in grid:
                d = dict(ps, Pref=P, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)
                A, st = gfm_A(d)
                if A is None: fs.append(None); continue
                m = swing_mode(A)
                if m is None: fs.append(None)
                else: fs.append(m[1]); last_osc = P
            seq = [(P, f) for P, f in zip(grid, fs) if f is not None]
            if len(seq) < 5: continue
            fr = [f for _, f in seq]
            tol = 0.005*(max(fr)-min(fr)+1e-12)
            is_mono = all(fr[i] >= fr[i+1]-tol for i in range(len(fr)-1))
            if is_mono: mono_ok += 1
            else:
                mono_bad += 1
                if len(badex) < 6:
                    i = next(i for i in range(len(fr)-1) if fr[i] < fr[i+1]-tol)
                    badex.append((name, Xgv, Vv, f"P={seq[i][0]:.2f}: {fr[i]:.2f}->{fr[i+1]:.2f}Hz"))
            if last_osc is not None:
                blind.append((pfold-last_osc)/pfold)
print(f"  单调降(0.5%容差): {mono_ok}/{mono_ok+mono_bad}  违例={mono_bad}")
for b in badex: print(f"    违例: {b}")
bl = np.array(blind)
print(f"  盲区宽度 (P_fold-P_末振)/P_fold: 中位={np.median(bl)*100:.1f}%  min={bl.min()*100:.1f}%  max={bl.max()*100:.1f}%  n={len(bl)}")

# ---------- B: GFL 折叠闭式 ----------
print()
print("== B: GFL P_SN=3V^2/4Xg vs 数值折叠 (二分平衡存在性) ==")
maxrel = 0
for Vv in (0.7, 0.85, 1.0, 1.15, 1.3):
    for Xgv in (0.1, 0.3, 0.6, 1.0, 1.5, 2.0):
        lo, hi = 0.01, 3*Vv*Vv/Xgv
        for _ in range(50):
            mid = 0.5*(lo+hi)
            if equilibrium_angle(mid, 0.0, Vv, Xgv) is None: hi = mid
            else: lo = mid
        pf = 0.75*Vv*Vv/Xgv
        rel = abs(lo-pf)/pf
        maxrel = max(maxrel, rel)
print(f"  30 点网格 (V:0.7-1.3, Xg:0.1-2.0): 最大相对偏差 = {maxrel:.2e}")

# ---------- C: GFL 分表盘 ----------
def drift4(x, P, Q, V, Xg, g):
    th, xp, Vdc, xi = x
    idr = g['kpv']*(1-Vdc) + g['kiv']*xi
    vgd = V*math.cos(th) - Xg*Q
    vgq = -V*math.sin(th) + Xg*idr
    Vs = Vdc if abs(Vdc) > 1e-6 else 1e-6
    return np.array([g['kp']*vgq + g['ki']*xp, vgq,
                     (P + 1.5*(vgd*idr + vgq*Q)/Vs)/g['C'], 1-Vdc])

def gfl_A(P, Q, V, Xg, g, h=1e-7):
    th = equilibrium_angle(P, Q, V, Xg)
    if th is None: return None
    x = np.array([th, 0.0, 1.0, V*math.sin(th)/Xg/g['kiv']])
    A = np.zeros((4, 4))
    for j in range(4):
        a = x.copy(); b = x.copy(); a[j] += h; b[j] -= h
        A[:, j] = (drift4(a, P, Q, V, Xg, g) - drift4(b, P, Q, V, Xg, g))/(2*h)
    return A

def eig_sorted(A, prev):
    ev = np.linalg.eigvals(A)
    if prev is None:
        return ev[np.argsort(-np.abs(ev.imag))]
    cost = np.abs(ev[:, None] - prev[None, :])
    r, c = linear_sum_assignment(cost)
    out = np.empty(4, complex); out[c] = ev[r]
    return out

GFL_GAINS = {
    "G1": dict(kp=50, ki=1000, kpv=1, kiv=50, C=0.01),
    "G2": dict(kp=20, ki=200, kpv=1, kiv=50, C=0.01),
    "G3": dict(kp=100, ki=4000, kpv=1, kiv=50, C=0.01),
    "G4": dict(kp=50, ki=1000, kpv=0.5, kiv=20, C=0.05),
    "G5": dict(kp=50, ki=1000, kpv=2, kiv=100, C=0.005),
    "G6": dict(kp=35, ki=600, kpv=1, kiv=50, C=0.01),
    "G7": dict(kp=10, ki=100, kpv=1, kiv=50, C=0.01),
    "G8": dict(kp=200, ki=8000, kpv=1, kiv=50, C=0.01),
    "G9": dict(kp=50, ki=1000, kpv=5, kiv=200, C=0.002),
    "G10": dict(kp=50, ki=1000, kpv=0.2, kiv=5, C=0.1),
}
print()
print("== C: GFL 逐支 f(P) 单调性 (0.5% 容差; 记方向) ==")
cm = {"mono_up": 0, "mono_dn": 0, "non_mono": 0}
nonex = []
for name, g in GFL_GAINS.items():
    for Xgv in (0.2, 0.5, 1.0):
        ps = 0.75/Xgv
        grid = np.linspace(0.15*ps, 0.999*ps, 500)
        prev = None; tracks = {k: [] for k in range(4)}
        for P in grid:
            A = gfl_A(P, 0, 1.0, Xgv, g)
            if A is None: break
            prev = eig_sorted(A, prev)
            for k in range(4): tracks[k].append(prev[k])
        # 找两个复对槽位(各取 Im>0 代表)
        done = set()
        for k in range(4):
            arr = np.array(tracks[k])
            if len(arr) < 10: continue
            if arr[0].imag <= 1.0: continue
            key = round(abs(arr[0].imag), 4)
            if key in done: continue
            done.add(key)
            fs = np.abs(arr.imag)/2/math.pi
            m = fs > 1e-3  # 只统计仍为复数的段
            fs = fs[m]
            if len(fs) < 10: continue
            tol = 0.005*(fs.max()-fs.min()+1e-12)
            up = all(fs[i] <= fs[i+1]+tol for i in range(len(fs)-1))
            dn = all(fs[i] >= fs[i+1]-tol for i in range(len(fs)-1))
            if up: cm["mono_up"] += 1
            elif dn: cm["mono_dn"] += 1
            else:
                cm["non_mono"] += 1
                if len(nonex) < 8:
                    nonex.append((name, Xgv, f"f0={fs[0]:.1f}Hz", f"范围[{fs.min():.1f},{fs.max():.1f}]"))
print(f"  分支统计: 单调升={cm['mono_up']}  单调降={cm['mono_dn']}  非单调={cm['non_mono']}")
for e in nonex: print(f"    非单调支: {e}")

# ---------- D: 时域抽查 ----------
print()
print("== D: 时域振铃 FFT vs 特征值频率 ==")
def ringing_freq(rhs, x0, T, n=8192):
    t = np.linspace(0, T, n)
    sol = solve_ivp(rhs, (0, T), x0, t_eval=t, rtol=1e-10, atol=1e-12, method='DOP853')
    y = sol.y[0] - sol.y[0][-1]
    y = y - y.mean()
    w = np.hanning(len(y))
    sp_ = np.abs(np.fft.rfft(y*w))
    fr = np.fft.rfftfreq(len(y), t[1]-t[0])
    i = 1 + int(np.argmax(sp_[1:]))
    return fr[i]

for name, Xgv, fracs in [("M1", 0.5, (0.2, 0.5, 0.8)), ("M9", 0.5, (0.2, 0.5, 0.8)), ("M4", 1.0, (0.2, 0.5, 0.8))]:
    ps = GFM_SETS[name]
    lo, hi = 0.01, 2.5/Xgv
    for _ in range(40):
        mid = 0.5*(lo+hi)
        d = dict(ps, Pref=mid, Qref=0.0, V=1.0, Xg=Xgv, Enom=1.0)
        if gfm_equil(d) is None: hi = mid
        else: lo = mid
    pfold = lo
    for fr_ in fracs:
        d = dict(ps, Pref=fr_*pfold, Qref=0.0, V=1.0, Xg=Xgv, Enom=1.0)
        A, st = gfm_A(d)
        if A is None: continue
        m = swing_mode(A)
        if m is None:
            print(f"  GFM {name} Xg={Xgv} P={fr_:.1f}pf: 摆模态已非振荡(盲区)"); continue
        lam, feig, _ = m
        if lam.real >= 0:
            print(f"  GFM {name} Xg={Xgv} P={fr_:.1f}pf: 不稳定点,跳过"); continue
        T = min(40.0, max(4.0, 6.0/abs(lam.real)))
        x0 = st.copy(); x0[0] += 0.02
        ftd = ringing_freq(lambda t, x: gfm_rhs(x, d), x0, T)
        print(f"  GFM {name} Xg={Xgv} P={fr_:.1f}pf: f_eig={feig:.3f}Hz  f_TD={ftd:.3f}Hz  差={abs(ftd-feig)/feig*100:.1f}%")

for name, Xgv, Ps in [("G1", 0.5, (0.4, 0.9)), ("G4", 1.0, (0.3, 0.55))]:
    g = GFL_GAINS[name]
    for P in Ps:
        A = gfl_A(P, 0, 1.0, Xgv, g)
        if A is None: continue
        ev = np.linalg.eigvals(A)
        cx = [e for e in ev if abs(e.imag) > 1.0 and e.real < 0]
        if not cx: continue
        lam = max(cx, key=lambda z: z.real)  # 最欠阻尼复模态 = 振铃主导
        feig = abs(lam.imag)/2/math.pi
        th = equilibrium_angle(P, 0, 1.0, Xgv)
        x0 = np.array([th+0.01, 0.0, 1.0, math.sin(th)/Xgv/g['kiv']])
        T = min(40.0, max(2.0, 6.0/abs(lam.real)))
        ftd = ringing_freq(lambda t, x: drift4(x, P, 0, 1.0, Xgv, g), x0, T)
        print(f"  GFL {name} Xg={Xgv} P={P}: f_eig={feig:.3f}Hz  f_TD={ftd:.3f}Hz  差={abs(ftd-feig)/feig*100:.1f}%")
