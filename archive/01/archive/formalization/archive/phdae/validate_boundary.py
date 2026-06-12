"""
Cross-validate stability boundary H_crit ≈ 4K + 8D√K
by numerically simulating the two-machine system and finding
the actual separatrix.
"""
import numpy as np
from scipy.integrate import solve_ivp
import json

def two_machine_ode(t, y, D, K):
    d1, d2, w1, w2 = y
    delta = d1 - d2
    s = np.sin(delta)
    dd1 = w1
    dd2 = w2
    dw1 = -D*w1 - K*s
    dw2 = -D*w2 + K*s
    return [dd1, dd2, dw1, dw2]

def H(y, K):
    d1, d2, w1, w2 = y
    return w1**2 + w2**2 + 2*K*(1 - np.cos(d1 - d2))

def find_separatrix(D, K, w_test_range, n_points=200):
    """Find the critical initial w1 (with d1=d2=0, w2=0) 
    that separates convergent from divergent trajectories."""
    
    w_low, w_high = w_test_range
    
    for _ in range(50):  # bisection
        w_mid = (w_low + w_high) / 2
        y0 = [0, 0, w_mid, 0]  # delta=0, w1=w_mid, w2=0
        
        sol = solve_ivp(two_machine_ode, [0, 200], y0, args=(D, K),
                       max_step=0.01, rtol=1e-10, atol=1e-12)
        
        delta_final = sol.y[0, -1] - sol.y[1, -1]
        
        # If delta exceeds pi, system went over the saddle
        delta_max = np.max(np.abs(sol.y[0] - sol.y[1]))
        
        if delta_max > np.pi:
            w_high = w_mid  # too much energy, went over
        else:
            w_low = w_mid   # stayed bounded
    
    return (w_low + w_high) / 2

results = {}

for K in [1.0, 0.5, 0.1, 0.05, 0.01]:
    for D in [0.0, 0.5, 1.0, 2.0]:
        # Conservative estimate
        H_conservative = 4*K
        w_conservative = 2*np.sqrt(K)
        
        # My approximate formula
        H_approx = 4*K + 8*D*np.sqrt(K)
        w_approx = np.sqrt(H_approx)
        
        # Numerical separatrix
        if D == 0:
            w_numerical = w_conservative  # exact for D=0
        else:
            try:
                w_numerical = find_separatrix(D, K, [w_conservative*0.5, w_conservative*5])
            except:
                w_numerical = float('nan')
        
        H_numerical = w_numerical**2  # H at delta=0, w2=0
        
        key = f"K={K},D={D}"
        results[key] = {
            "K": K, "D": D,
            "w_conservative": round(w_conservative, 4),
            "w_approx": round(w_approx, 4),
            "w_numerical": round(w_numerical, 4),
            "H_conservative": round(H_conservative, 4),
            "H_approx": round(H_approx, 4),
            "H_numerical": round(H_numerical, 4),
        }

# Print table
print("| K | D | w_conservative | w_approx | w_numerical | approx_error |")
print("|---|---|---|---|---|---|")
for key, r in results.items():
    if r['w_numerical'] > 0:
        err = abs(r['w_approx'] - r['w_numerical']) / r['w_numerical'] * 100
    else:
        err = float('nan')
    print(f"| {r['K']} | {r['D']} | {r['w_conservative']:.3f} | {r['w_approx']:.3f} | {r['w_numerical']:.3f} | {err:.1f}% |")

