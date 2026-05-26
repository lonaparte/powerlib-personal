# 电力电子化电力系统的形式化：已验证的认知

> 2026.05 | 只包含经过验证的结论和诚实的未知

---

## 做了什么

对两机非线性系统（sin 耦合、droop 阻尼）用 KeYmaera X 和数值分析做了完整的稳定性探索。

### 系统

$$\dot{\delta} = \omega_1 - \omega_2, \quad \dot{\omega}_1 = -D_1\omega_1 - K\sin\delta, \quad \dot{\omega}_2 = -D_2\omega_2 + K\sin\delta$$

这是消去代数变量后的约化 ODE，不是 DAE。

KeYmaera X 中用辅助变量 s = sinδ, c = cosδ，附加不变量 s²+c²=1。H = ω₁²+ω₂²+2K(1−c)。

---

## 已验证的结论

### 1. pH 结构使能量平衡中 sin 项精确抵消

$$\dot{H} = -2D_1\omega_1^2 - 2D_2\omega_2^2$$

（因子 2 来自 H 的定义：H = ω₁²+ω₂²+2K(1−cosδ)，不含 1/2 系数。若用物理惯例 H_phys = (1/2)(ω₁²+ω₂²)+K(1−cosδ) = H/2，则 Ḣ_phys = −D₁ω₁²−D₂ω₂²。）

**验证方式**：

- **代数等式**：Lean 4 直接证明 ∇H_phys·(J−R)∇H_phys = −(R₁₁x₁²+R₂₂x₂²)（`PHEnergyBalance.lean`，对应 H_phys 惯例）。
- **动力学后果**：KeYmaera X 证明 H 的任意亚水平集沿 ODE 正不变（`parametric.kyx`，符号参数 J₁,J₂,D₁,D₂,K > 0）。dI 策略成功要求 Ḣ ≤ 0，而 Ḣ ≤ 0 在 D₁,D₂ > 0 时等价于 sin 项精确抵消。

注意：KeYmaera X 验证的是 Ḣ ≤ 0（不等式），不是 Ḣ = −2D₁ω₁²−2D₂ω₂²（等式）。等式本质上是代数恒等式（Lean 4 证明覆盖）。两者互补。

### 2. D₁ > 0, D₂ > 0 时的 Lyapunov 稳定性

H 的亚水平集正不变，即 H(x(0)) < ε → H(x(t)) < ε，∀t ≥ 0。

**KeYmaera X 证明**：

- **符号参数**（`parametric.kyx`）：∀J₁,J₂,D₁,D₂,K > 0，H < bound → [ODE] H < bound。dI 一步完成。
- **完整 ∀ε∃δ 形式**（`lyapunov_nonlinear.kyx`）：以 H 本身为度量，δ = ε。仅 K=D₁=D₂=1。
- **分量形式 ∀ε∃δ**（`lyapunov_complete.kyx`）：ω₁²<ε, ω₂²<ε, 1−cosδ<ε，δ = ε/4。仅 K=D₁=D₂=1。

**参数范围限制**：完整的 ∀ε∃δ Lyapunov 稳定性（分量形式）仅对 K=D₁=D₂=1 验证。符号参数版本只证明了亚水平集不变性（等价，但形式较弱）。原因：δ 的选取依赖 K 的具体值（δ = ε/(2+2K)），KeYmaera X 的 existsR 策略需要显式 witness。

### 3. D₁ > 0, D₂ > 0 时的渐近稳定性

修正 Hamiltonian V = H + (ω₁−ω₂)sinδ/4 在 {cosδ ≥ 0} 域内满足 V(t) ≤ V₀ − t·target/12，从而系统在有限时间内使 V 降到任意 target > 0 以下。

**KeYmaera X 证明（4 个文件组合）**：

1. `asymptotic_closed.kyx`：主定理。在域 {s²+c²=1, c≥0, V≥target} 内证明 V 线性下降，时间有界。dC + dI。
2. `aux_v_implies_c.kyx`：V < 1 → c > 0。纯代数，QE 验证。
3. `aux_strict_decay.kyx`：V̇ + (ω₁²+ω₂²+s²)/4 ≤ 0 在 {c≥0} 内。QE 验证。
4. `aux_v_upper_bound.kyx`：V ≤ 3(ω₁²+ω₂²+s²) 在 {c≥0} 内。QE 验证。

**论证闭合**：主定理证明系统在有限时间内离开 {c≥0 ∧ V≥target}。出口可能是 V < target（好）或 c < 0（坏）。由辅助引理 (2)：V < 1 → c > 0，且 V(t) ≤ V₀ < 1 始终成立（由 dC），所以 c > 0 始终维持，出口只能是 V < target。

**参数范围限制**：仅对 K=D₁=D₂=1 验证。另有 `parametric_asymptotic.kyx` 对 D₁=1,D₂=5,K=2 验证（时间界 48V₀/target）。一般性 ∀D₁,D₂,K > 0 的渐近稳定性未在 KeYmaera X 中证明。原因：修正 Hamiltonian 的系数 a 和时间界 C 依赖于参数，QE 需要处理含多个符号参数的多项式不等式，目前未找到适用于所有参数的统一 witness。

### 4. 稳定域

- **不变性**：H < 4K 沿 ODE 正不变（`stability_boundary.kyx`，D=K=1）。dI 一步完成。
- **D=0 时 H 精确守恒**：H(t) = H(0)（`necessary_d0.kyx`，符号 K > 0），因此 H < 4K 对保守系统平凡不变。
- **H = 4K 的物理意义**：对应 δ = π 的鞍点能量（2K(1−cos π) = 4K）。这是拓扑论证：鞍点能量是分离线的能量水平。**KeYmaera X 未证明 tightness**（即 H = 4K 时确实存在逃逸轨迹）。
- **耗散系统（D>0）**：实际稳定域比 H < 4K 更大，但无闭式表达。

### 5. D > 0 ∧ K > 0 是渐近稳定的充要条件（对称情形 D₁=D₂=D）

**充分性**（D > 0, K > 0 → 渐近稳定）：

由结论 3 的 KeYmaera X 证明给出，但仅覆盖特定参数值（K=D=1 和 D₁=1,D₂=5,K=2）。一般性充分性证明未完成（见结论 3 的参数范围限制）。

**必要性——D = 0**（`necessary_d0.kyx`，符号 K > 0）：

D=0 时 H 精确守恒（Ḣ=0），H(0)>0 的轨迹永远不到达原点。dI 一步完成。

**必要性——D < 0**（`necessary_dneg.kyx`，符号 D < 0, K > 0）：

D<0 时 Ḣ = −2D(ω₁²+ω₂²) > 0（当 ω₁²+ω₂²>0），能量严格增长。系统不稳定。dI 一步完成。

**必要性——K = 0**（`necessary_k0.kyx`，符号 D₁,D₂ > 0）：

K=0 时无耦合恢复力。守恒量 u = D₁D₂(d₁−d₂)+D₂ω₁−D₁ω₂ 沿 ODE 不变（Lie 导数 = D₁D₂(ω₁−ω₂)+D₂(−D₁ω₁)−D₁(−D₂ω₂) = 0）。若 u(0) ≠ 0，则 (d₁−d₂, ω₁, ω₂) 永远不能同时为零，系统不收敛到平衡点。dC + dW + QE。

---

## 已排除的假问题

| 声称的问题 | 排除原因 |
|-----------|---------|
| Q 矩阵奇异 | 全局角度平移对称性，固定参考角后 Q 正定（det=1） |
| Dirac 结构组合困难 | 逐点应用即可，无额外困难 |
| Schur 补标量模型的稳定性边界 | 模型不代表电力系统 + 符号搞反，结论完全错误 |
| 摄动公式 H_crit ≈ 4K + 8D√K | 数值交叉验证误差 30-80% |
| sin 限幅使线性不稳定系统非线性稳定 | 仿真时间不足导致的假象，更长时间仿真推翻 |

---

## 形式化的猜想（有 Problem 无 Tactic）

以下命题已用 dL 形式化为 .kyx 文件的 Problem 块，但尚未证明。形式化语句是精确的；自然语言仅为辅助理解。

### C1. 一般参数渐近稳定性（`conjecture_parametric_asymptotic.kyx`）

∀D₁,D₂,K > 0, ∃a,C > 0：修正 Hamiltonian V = H+a(ω₁−ω₂)sinδ 在有限时间 C·V₀/target 内使 V 降到 target 以下。

已证实例：K=D=1 (a=1/4, C=12)，D₁=1,D₂=5,K=2 (a=1/4, C=48)。
瓶颈：existsR 需要 a(D₁,D₂,K) 和 C(D₁,D₂,K) 的显式 witness。

### C2. Routh 边界外的不稳定性（`conjecture_instability_boundary.kyx`）

D₁>0, K>0, D₂<0, D₁D₂+K ≤ 0 时：∀ε>0, ∃初始条件在 {H<ε} 内，轨迹到达 {H>2ε}（菱形模态）。

即 Routh-Hurwitz 第二条件 D₁D₂+K>0 不满足时，系统局部不稳定。
瓶颈：菱形证明需要 dG（微分鬼变量）构造显式逃逸轨迹。

### C3. D₂<0 局部渐近稳定性（`conjecture_neg_d2_lyapunov.kyx`）

D₁=1, D₂=−3/10, K=1 的具体实例。V = x'Px（精确有理数 P 矩阵来自 A'P+PA=−I）在 {V<1/10, c>0} 域内 V̇ ≤ −target/100。

这是 D₂<0 时用非 pH 方法的局部稳定性证明。
瓶颈：QE 需要处理 s²+c²=1 约束下的 4 次多项式不等式。

### C4. pH 结构的 Lyapunov 函数存在性（`conjecture_ph_bridge.kyx`）

**核心研究问题**。D₁=1, D₂=−3/10, K=1：∃a,b 使得 V = H + a(ω₁−ω₂)s + b·ω₂·s 在 {c≥1/2} 域内 V̇ < 0。

如果存在：pH 结构可以推广到非全无源系统。
如果不存在：pH 结构在 D₂<0 时本质上无法提供 Lyapunov 函数。

### 未形式化的结论（仅数值/解析）

| 结论 | 验证方式 | 形式化状态 |
|------|---------|-----------|
| D₂<0 时 H 不是 Lyapunov 函数 | Ḣ = −2D₁ω₁²+2\|D₂\|ω₂² 不定，解析显然 | 可形式化但平凡 |
| x'Px 稳定域随 \|D₂\| 增大收缩 | Taylor 余项数值估计 | 未形式化 |
| Routh-Hurwitz 边界 \|D₂\|<min(D₁,K/D₁) | 手工推导+12 组数值验证 | 未形式化（线性代数，非 dL 原生） |
| Lur'e 圆判据/Popov 判据太保守 | 数值频域分析 | 不可直接 dL 形式化（频域概念） |

### 没做到的

- 没有在 DAE 层面（不消去代数变量）直接做分析
- 没有做 N > 2 台机器的情况
- 没有做异构设备（构网 + 跟网 + 同步机混合）
- 没有做实际控制器结构（PLL 的具体动态，而非等效负阻尼）

---

## 文件索引

### 已证明（有 Tactic，KeYmaera X 通过）

| 结论 | 文件 | 参数范围 | 策略 |
|------|------|---------|------|
| 1. Ḣ ≤ 0 | `parametric.kyx` | 符号 J,D,K > 0 | dI |
| 1. 代数等式 | `PHEnergyBalance.lean` | 2×2 整数矩阵 | ring-style |
| 2. 亚水平集不变 | `parametric.kyx` | 符号 J,D,K > 0 | dI |
| 2. ∀ε∃δ (H 度量) | `lyapunov_nonlinear.kyx` | K=D=1 | existsR + dI |
| 2. ∀ε∃δ (分量) | `lyapunov_complete.kyx` | K=D=1 | existsR + dC + dI |
| 3. 渐近稳定 | `asymptotic_closed.kyx` + aux_*.kyx | K=D=1 | dC + dI + QE |
| 3. 渐近稳定 | `parametric_asymptotic.kyx` | D₁=1,D₂=5,K=2 | dC + dI + QE |
| 4. H<4K 不变 | `stability_boundary.kyx` | D=K=1 | dI |
| 5. D=0 必要 | `necessary_d0.kyx` | 符号 K > 0 | dI |
| 5. D<0 必要 | `necessary_dneg.kyx` | 符号 D < 0, K > 0 | dI |
| 5. K=0 必要 | `necessary_k0.kyx` | 符号 D₁,D₂ > 0 | dC + dW + QE |

### 猜想（有 Problem 无 Tactic）

| 猜想 | 文件 | 核心困难 |
|------|------|---------|
| C1. 一般参数渐近稳定 | `conjecture_parametric_asymptotic.kyx` | existsR 需参数化 witness |
| C2. Routh 边界外不稳定 | `conjecture_instability_boundary.kyx` | 菱形模态需 dG 构造逃逸轨迹 |
| C3. D₂<0 局部 x'Px 稳定 | `conjecture_neg_d2_lyapunov.kyx` | QE 处理 4 次多项式 + s²+c²=1 |
| C4. pH 结构 Lyapunov 函数 | `conjecture_ph_bridge.kyx` | 核心研究问题：是否存在 |

---

## 方法论认知

1. **形式化验证（KeYmaera X）对全无源 pH 系统非常有效**。dI + dC + QE 可以自动证明 Lyapunov 和渐近稳定性。微分不变量绕过了 ODE 解理论。

2. **pH 结构的真正价值是代数简化**：sin 项的精确抵消将非线性能量分析化简为二次型问题。但这不等于稳定性——二次型不定时需要额外工具。

3. **交叉验证是必需的**。每一个未经验证的结论都有可能是错的。这次发现的错误包括：符号搞反、公式只对特定参数正确、仿真时间不足造成假象。

4. **参数特化 vs 一般性是实际瓶颈**。KeYmaera X 的 existsR 策略需要显式 witness，当 witness 依赖符号参数时（如 δ=ε/(2+2K)），证明可能需要手工参数化。渐近稳定性的修正 Hamiltonian 系数和时间界都依赖参数，导致一般性证明困难。

5. **"难点在哪"这个问题本身需要不断修正**。从最初的"10个障碍"到最后的"1个核心问题"，每一轮推敲都排除了假问题或发现了新问题。当前的认知仍可能有错。
