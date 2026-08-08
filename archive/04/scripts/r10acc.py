"""R10 公式精度大范围测试:
GFL: zeta_pred=(kp/2)sqrt(Vcos/ki)  vs 全模型 PLL 模态实测 zeta
GFM: zeta_pred=D/(2 sqrt(MK))       vs 全模型摆模态实测 zeta
另测单调性断言: GFL zeta(V) 升 / GFM zeta(V) 降 (固定绝对 P)
"""
import numpy as np, math
from scipy.optimize import fsolve
from gfl_operating_point_stability_sim.analysis import equilibrium_angle

# ---------------- GFL ----------------
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
    if th is None: return None, None
    x = np.array([th, 0.0, 1.0, V*math.sin(th)/Xg/g['kiv']])
    A = np.zeros((4, 4))
    for j in range(4):
        a = x.copy(); b = x.copy(); a[j] += h; b[j] -= h
        A[:, j] = (drift4(a, P, Q, V, Xg, g) - drift4(b, P, Q, V, Xg, g))/(2*h)
    return A, th

def mode_zeta(A, states):
    """参与因子在 states 上份额>0.5 的复模态: 返回 (zeta, f, share);无则 None"""
    lam, Vr = np.linalg.eig(A)
    Wl = np.linalg.inv(Vr)
    best = None
    for k in range(4):
        if abs(lam[k].imag) < 1e-6: continue
        p = np.abs(Vr[:, k]*Wl[k, :]); p = p/p.sum()
        sh = sum(p[s] for s in states)
        if sh > 0.5 and (best is None or sh > best[2]):
            z = -lam[k].real/abs(lam[k])
            best = (z, abs(lam[k].imag)/2/math.pi, sh)
    return best

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
print("== GFL: zeta 公式精度 (ratio = 实测/公式) ==")
ratios = {}
nmode_missing = 0
for name, g in GFL_GAINS.items():
    for Xg in (0.2, 0.5, 1.0):
        for V in (0.8, 1.0, 1.2):
            psn = 0.75*V*V/Xg
            for frac in (0.3, 0.7):
                P = frac*psn
                A, th = gfl_A(P, 0, V, Xg, g)
                if A is None: continue
                m = mode_zeta(A, (0, 1))
                if m is None: nmode_missing += 1; continue
                zp = 0.5*g['kp']*math.sqrt(V*abs(math.cos(th))/g['ki'])
                if zp > 1: continue  # 公式预测过阻尼,无可比振荡模态
                ratios.setdefault(Xg, []).append((m[0]/zp, name, V, frac))
for Xg in sorted(ratios):
    r = np.array([t[0] for t in ratios[Xg]])
    print(f"  Xg={Xg}: n={len(r)}  中位={np.median(r):.2f}  min={r.min():.2f}  max={r.max():.2f}")
print(f"  (无可识别 PLL 复模态而跳过: {nmode_missing} 点)")

print()
print("== GFL: zeta(V) 单调升检验 (固定绝对 P, V=0.8..1.2) ==")
viol = 0; tot = 0; vioex = []
for name, g in GFL_GAINS.items():
    for Xg in (0.2, 0.5, 1.0):
        for frac in (0.3, 0.6):
            P = frac*0.75*0.8*0.8/Xg  # 以 V=0.8 的 SN 为基准取绝对 P
            zs = []
            for V in (0.8, 0.9, 1.0, 1.1, 1.2):
                A, th = gfl_A(P, 0, V, Xg, g)
                if A is None: zs = None; break
                m = mode_zeta(A, (0, 1))
                if m is None: zs = None; break
                zs.append(m[0])
            if zs is None: continue
            tot += 1
            if not all(zs[i] <= zs[i+1] + 1e-9 for i in range(4)):
                viol += 1; vioex.append((name, Xg, frac, [round(z, 4) for z in zs]))
print(f"  组合数={tot}  违例={viol}")
for v in vioex[:8]: print(f"    违例: {v}")

# ---------------- GFM ----------------
import sympy as sp
delta, omega, Pf, Qf = sp.symbols('delta omega Pf Qf', real=True)
Pref, Qref, V, Xg, M, D, mq, wc, Enom = sp.symbols('Pref Qref V Xg M D mq wc Enom', positive=True)
E = Enom - mq*(Qf - Qref)
Pe = E*V/Xg*sp.sin(delta); Qe = (E**2 - E*V*sp.cos(delta))/Xg
f = sp.Matrix([omega, (Pref - Pf - D*omega)/M, wc*(Pe - Pf), wc*(Qe - Qf)])
x = sp.Matrix([delta, omega, Pf, Qf]); J = f.jacobian(x)
args = (delta, omega, Pf, Qf, Pref, Qref, V, Xg, M, D, mq, wc, Enom)
f_l = sp.lambdify(args, f, 'numpy'); J_l = sp.lambdify(args, J, 'numpy')

def gfm_equil(d):
    def res(z):
        st = [z[0], 0.0, d['Pref'], z[1]]
        r = np.array(f_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                         d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float).ravel()
        return [r[2], r[3]]
    for dl0 in (0.1, 0.3, 0.6, 0.9, 1.2):
        z, info, ier, msg = fsolve(res, [dl0, 0.0], full_output=True)
        st = np.array([z[0], 0.0, d['Pref'], z[1]])
        r = np.array(f_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                         d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float).ravel()
        if ier == 1 and np.max(np.abs(r)) < 1e-9 and 0 < z[0] < np.pi/2:
            return st
    return None

def gfm_A(d):
    st = gfm_equil(d)
    if st is None: return None, None, None
    A = np.array(J_l(*st, d['Pref'], d['Qref'], d['V'], d['Xg'],
                     d['M'], d['D'], d['mq'], d['wc'], d['Enom']), float)
    Estar = d['Enom'] - d['mq']*(st[3] - d['Qref'])
    K = Estar*d['V']*math.cos(st[0])/d['Xg']
    return A, st, K

GFM_SETS = {
    "M1": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*31),
    "M2": dict(M=0.1, D=0.2, mq=0.05, wc=2*math.pi*10),
    "M3": dict(M=0.005, D=0.02, mq=0.2, wc=2*math.pi*100),
    "M4": dict(M=0.05, D=0.5, mq=0.1, wc=2*math.pi*5),
    "M5": dict(M=0.02, D=0.02, mq=0.1, wc=2*math.pi*20),
    "M6": dict(M=0.02, D=0.05, mq=0.0, wc=2*math.pi*31),   # 无下垂
    "M7": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*200),  # 极快滤波
    "M8": dict(M=0.02, D=0.05, mq=0.1, wc=2*math.pi*3),    # 极慢滤波
    "M9": dict(M=0.5, D=1.0, mq=0.05, wc=2*math.pi*31),    # 大惯量
    "M10": dict(M=0.002, D=0.1, mq=0.1, wc=2*math.pi*50),  # 小惯量强阻尼
}
print()
print("== GFM: zeta 公式精度 (按 wc 分组; ratio = 实测/公式) ==")
gratios = {}
gmiss = 0
for name, ps in GFM_SETS.items():
    for Xgv in (0.2, 0.5, 1.0):
        for Vv in (0.8, 1.0, 1.2):
            pmax = 1.0*Vv/Xgv
            for frac in (0.2, 0.5):
                d = dict(ps, Pref=frac*pmax, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)
                A, st, K = gfm_A(d)
                if A is None: continue
                m = mode_zeta(A, (0, 1))
                if m is None: gmiss += 1; continue
                zp = ps['D']/(2*math.sqrt(ps['M']*K))
                if zp > 1: continue
                fcHz = ps['wc']/2/math.pi
                gratios.setdefault(fcHz, []).append((m[0]/zp, name, Vv, Xgv, frac))
for fc in sorted(gratios):
    r = np.array([t[0] for t in gratios[fc]])
    print(f"  fc={fc:.0f}Hz: n={len(r)}  中位={np.median(r):.2f}  min={r.min():.2f}  max={r.max():.2f}")
print(f"  (无可识别摆模态而跳过: {gmiss} 点)")

print()
print("== GFM: zeta(V) 单调降检验 (固定绝对 Pref, V=0.8..1.2) ==")
gviol = 0; gtot = 0; gvioex = []
for name, ps in GFM_SETS.items():
    for Xgv in (0.2, 0.5, 1.0):
        for frac in (0.2, 0.4):
            Prefv = frac*1.0*0.8/Xgv
            zs = []
            for Vv in (0.8, 0.9, 1.0, 1.1, 1.2):
                d = dict(ps, Pref=Prefv, Qref=0.0, V=Vv, Xg=Xgv, Enom=1.0)
                A, st, K = gfm_A(d)
                if A is None: zs = None; break
                m = mode_zeta(A, (0, 1))
                if m is None: zs = None; break
                zs.append(m[0])
            if zs is None: continue
            gtot += 1
            if not all(zs[i] >= zs[i+1] - 1e-9 for i in range(4)):
                gviol += 1; gvioex.append((name, Xgv, frac, [round(z, 4) for z in zs]))
print(f"  组合数={gtot}  违例={gviol}")
for v in gvioex[:10]: print(f"    违例: {v}")
