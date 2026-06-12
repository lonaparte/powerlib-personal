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

## 单机系统（SMIB）：完整的大信号分析

两机系统消去公共模态后，单机对无穷大母线（SMIB）是最基础的暂态稳定性对象。控制方式为**下垂/等效阻尼**（droop / effective damping）：δ′=ω, ω′=Pm−Dω−Ksinδ（阻尼力矩 −Dω 来自下垂控制或等效阻尼，不是同步机的精确电磁阻尼）。全部**大信号、非线性、不做线性化假设**，能参数化的全参数化。

H = ω²+2K(1−cosδ)（与两机同惯例，不含 1/2）。

### S1. 保守情形 D=0：能量精确守恒

∀K>0，Ḣ=0，H(t)=H(0)（`smib_conservative.kyx`，符号 K，dI）。无阻尼时轨迹沿等能量线运动。

### S2. 正阻尼 D>0：Lyapunov 稳定 + 稳定域

- **亚水平集不变**：∀D,K>0，{ω²+2K(1−cosδ)<1} 正不变（`smib_passive_lyapunov.kyx`，符号 D,K，dI）。
- **稳定域 H<4K**：∀D,K>0，{H<4K} 正不变（`smib_region_4K.kyx`，符号 D,K，dI）。H=4K 是 δ=π 鞍点（分离线）的能量水平。

### S3. 正阻尼 D>0：渐近稳定

- **实例 D=K=1**：修正 Lyapunov V=H+(1/2)ωsinδ 在 {cosδ≥0} 内 V̇<0，有限时间 t<3V₀/target 收敛（`smib_asymptotic.kyx`，dC+dI）。大信号轨迹级 dL 证明。
- **参数化代数条件**：∀D,K>0, c∈[0,1]，取 a=DK/(K+D²)，负定/正定条件 DKc−2D(K+D²)<0、7D²/4+K(2−c)>0、K(K+D²)²−D²K²/4>0 全部成立（`smib_asymptotic_parametric.kyx`，QE）。**注意：这只证明了修正 Lyapunov 函数的（半）负定性代数条件，不是轨迹级 dL 证明**——一般参数的轨迹级证明仍受 existsR witness 瓶颈限制（与两机 C1 同源）。

### S4. 负阻尼 D<0：能量严格增长（不稳定）

∀D<0,K>0，当 ω≠0 时 Ḣ=−2Dω²>0，H(t)≥H(0)（`smib_negdamping_unstable.kyx`，符号 D,K，dI）。单机无被动伙伴可耦合，能量单调注入，原点不可能被任何能量论证镇定——大信号下真实不稳定。（这是大信号能量证书；Chetaev 二次型 x′Qx 只是其局部线性化版本，因"不做线性化"要求未单独形式化。）

### S5. 带载（Pm≠0）：大信号能量不变 + 平衡点渐近稳定

- **大信号不变量**：∀D,K, |Pm| 任意，修正能量 V=ω²+2K(1−cosδ)−2Pmδ 满足 V̇=−2Dω²（Pm 项在 Lie 导数中精确抵消），D≥0 时亚水平集不变（`smib_tilted_largesignal.kyx`，dI）。
- **带载平衡点渐近稳定**：|Pm|<K 时存在稳定平衡 δ_s（sinδ_s=Pm/K），有效同步系数 Ke=√(K²−Pm²)=Kcosδ_s>0。移轴后结构与无载 SMIB 同（K→Ke）。∀D>0, Ke>0 平衡点渐近稳定（`smib_loaded_equilibrium.kyx`，QE）。**同 S3 参数化版：证明的是 (D,Ke) 参数化的负定/正定代数条件，非轨迹级 dL 证明**。

### S6. 失步（Pm>K）：频率发散

无阻尼 D=0 且 Pm>K 时 sinδ=Pm/K 无解，无平衡点。∀K>0,Pm>K，ω−(Pm−K)t 非减，故 ω(t)≥ω₀+(Pm−K)t→+∞（`smib_loss_of_synchronism.kyx`，符号 K,Pm，dC+dW+QE+dI）。大信号、精确非线性的失步证明。

**单机小结**：保守(S1)/欠阻尼稳定(S2,S3)/负阻尼不稳定(S4)/带载平衡(S5)/失步(S6) 覆盖了 SMIB 全部定性区域。轨迹级大信号 dL 证明：S1,S2,S4,S6 全参数符号化；S3,S5 渐近稳定为实例级轨迹证明 + 参数化代数条件（轨迹级一般化受 existsR witness 限制）。

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

### C4. pH 结构的 Lyapunov 函数存在性 —— 已解决（YES）

**核心研究问题，已解决**。D₂<0 时存在 pH 结构的 Lyapunov 函数：

$$V = H + h\sin^2\delta + a_1\omega_1\sin\delta + a_2\omega_2\sin\delta$$

- **加上 sin²δ 后存在**：参数化证明 `theorem_ph_parametric.kyx`（∀D₁,K,d，M(1)≺0）+ 实例 `theorem_ph_bridge.kyx`（d=3/10 的非线性 dI）。
- **sin²δ 项何时必需**：参数化后发现是 **d 相关的**，不是普适的（见下表）。

**四带参数化结构**（D₁=K=1，d=|D₂|，符号推导）：

| 范围 | 修正需求 | 状态 |
|------|---------|------|
| d < 0.225 | 2 参数族（**无 sin²**）即可 | 数值（d_thresh≈0.225 由 minor 边界定） |
| 0.225 < d < d_LMI | **需 sin²**（3 参数）；2 参数族可证不行 | `impossibility_ph_linear.kyx`（d=3/10 实例 ✅） |
| d_LMI < d < 1.0 | 间隙：连 3 参数也不行，须用非 pH 的 x'Qx | `gap_no_ph_lyapunov.kyx`（d=19/20 实例 ✅） |
| d ≥ 1.0 | 系统不稳定 | Routh |

sin² 项**只在中间带 (0.225, 0.8899) 必需**。早期"sin² 普适必需"的说法是基于 d=3/10 单点，参数化暴露了它的 d 依赖性。

**充分条件 (2D₁+3d)²<16K 的参数化证明**：`theorem_ph_parametric.kyx` + `det_factorization.kyx`，∀D₁,K,d，三个 Sylvester 子式 D₁−d、7(D₁−d)²/16、7(D₁−d)³(16K−(2D₁+3d)²)/512 全部闭式。

**大信号 + 参数化的补足（`theorem_ph_bridge_parametric.kyx`）**：以上参数化证明全部在 c=cosδ=1 处取值，即**线性化**于平衡点；`theorem_ph_bridge.kyx` 的非线性大信号不变性又只证了**固定实例** d=3/10。缺的一块是"大信号 ∧ 参数化"。关键结构：V̇=x′M(c)x，M(c) **关于 c 仿射**，故在 c∈[4/5,1] 上 V̇ 是两端点的凸组合 → V̇≤0 在整段大信号域上 ⟺ 两端点 V̇≤0。本文件用纯全称 QE 证明 ∀d∈(0,2/5]，c=1 与 c=4/5 两端点的二次型均负半定（Lie 导数已独立用 sympy 从 V 与 ODE 重算核验，两端点恰为 6V̇|₍c=1₎ 与 30V̇|₍c=4/5₎）；再由仿射凸组合（一行恒等式）得 V̇≤0 在 c∈[4/5,1] 整段大信号域上、对全部 d∈(0,2/5] 成立。2/5=Routh 边界(d<1)的 40%（此固定闭式证书在 c≥4/5 上的精确上限是 d≈0.441）。

**更新（本会话，缺失象限已闭合）**：完整的 box 亚水平集不变性 `[ODE]{V<1/25}` 现已**参数化**证明（`theorem_ph_bridge_invariant_parametric.kyx`，∀d∈(0,2/5]，KeYmaera X 5.1.2 实跑 PROVED，qe=367ms）。朴素写法（演化域含圆等式 s²+c²=1）的 5 变量 dI QE 在 Z3 下确实证不动（实测 >8min 无果）；关键观察是 V̇≤0 在 slab c∈[4/5,1] 上**无约束**成立（不需 s²+c²=1，最坏特征值 −1.9e−2），而动力学守恒 s²+c²，故取演化域为 slab `{c≥4/5 & c≤1}`，dI 的 QE 退化为纯 box（无等式簇），0.58s 通过。至此大信号"下降"与"亚水平集不变"**均为参数化**（此前只有下降是）。数值在 d∈{0.1,0.25,0.4} 物理轨迹上交叉验证通过。

**d_LMI = 0.88988155**（代数数）。严格刻画：3 参数族上最优的 M=A'P+PA 恰好变成**秩 1 负半定**（特征值 [−0.22, 0, 0]）的 d 值。秩 1 条件（4 个多项式方程）消去 (a₁,a₂,h) 后得到 d 的多项式，d_LMI 是其根。秩 1 求解（0.88988155）与 λ_max 优化（0.88988157）吻合到 7 位。

- 间隙 **[d_LMI, 1) ≈ [0.8899, 1)**：系统稳定但 3 参数 pH 族**不存在** V（min λ_max > 0，必须用一般 x'Qx）。这是真实的、不依赖条件数的内在间隙。
- 间隙 [0.67, d_LMI)：pH 结构的 V 存在但随 d→d_LMI 退化（稳定域估计收缩到零）。

**重要修正**：(2D₁+3d)²<16K 是**良态充分条件**（d~0.67），不是紧边界。pH-LMI 极限是 d_LMI~0.8899（此处 V 退化）。边界数值依赖对 V 条件数的要求——没有单一的"紧边界"，而是覆盖率与 V 质量的权衡。但 **[d_LMI, 1) 的不可行性是内在的**（对此 3 参数族）。

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

## 文件索引（KeYmaera X 5.1.2 实跑结果）

> **文件位置(2026-06-12 迁移)**:所有**机器验证通过**(`.kyp` 含 `\qed`)的 104 个 .kyx+.kyp 已按审计流程迁至仓库根
> `01/{smib,two_machine,three_machine,four_machine}/`,编译通过的 Lean 证明在 `01/lean/`(迁移依据与复验记录见 `01/README.md`:
> 104/104 串行 fresh 重跑一致 + 新位置抽样重证)。**未走完流程的**(10 个 OPEN + 4 个 conjecture + 探索性 Lean)留在
> `formalization/archive/phdae/`。下文各表中的文件名不变,仅目录前缀按此规则解读。

### ✅ 机器已验证 PROVED（14 个）

| 结论 | 文件 | 参数范围 | 策略 |
|------|------|---------|------|
| Ḣ ≤ 0 / 亚水平集不变 | `parametric.kyx` | 符号 J,D,K > 0 | dI |
| 代数等式 ∇H'(J-R)∇H | `PHEnergyBalance.lean` | 2×2 整数矩阵 | ring-style |
| ∀ε∃δ (H 度量) | `lyapunov_nonlinear.kyx` | K=D=1 | existsR + dI |
| ∀ε∃δ (分量) | `lyapunov_complete.kyx` | K=D=1 | existsR + dC + dI |
| 非线性渐近稳定 | `asymptotic_closed.kyx` | K=D=1 | dC + dI + QE |
| 异构渐近稳定 | `parametric_asymptotic.kyx` | D₁=1,D₂=5,K=2 | dC + dI + QE |
| H<4K 不变 | `stability_boundary.kyx` | D=K=1 | dI |
| 基本非线性稳定 | `two_machine_nonlinear.kyx` | K=D=1 | dI |
| D=0 必要 | `necessary_d0.kyx` | 符号 K > 0 | dI |
| D<0 必要 | `necessary_dneg.kyx` | 符号 D < 0, K > 0 | dI |
| K=0 必要 | `necessary_k0.kyx` | 符号 D₁,D₂ > 0 | dC + dW + QE |
| **pH Lyapunov for D₂<0** | `theorem_ph_bridge.kyx` | D₁=K=1, d=3/10 | dI（核心结果） |
| **(2D₁+3d)²<16K 代数基础** | `det_factorization.kyx` | 符号 D₁,K | QE |
| **sin²δ 修正不可或缺** | `impossibility_ph_linear.kyx` | d=3/10 | QE（Sylvester 析取） |
| **pH 桥大信号 V̇≤0（参数化 d）** | `theorem_ph_bridge_parametric.kyx` | D₁=K=1, d∈(0,2/5] | QE（两端点 + 仿射） |
| **pH 桥大信号亚水平集不变（参数化 d）** | `theorem_ph_bridge_invariant_parametric.kyx` | D₁=K=1, d∈(0,2/5] | dI（slab 演化域→box QE） |

### ✅ 单机 SMIB 机器已验证 PROVED（9 个）

| 结论 | 文件 | 参数范围 | 策略 |
|------|------|---------|------|
| D=0 能量守恒 | `smib_conservative.kyx` | 符号 K | dI |
| D>0 亚水平集不变 | `smib_passive_lyapunov.kyx` | 符号 D,K | dI |
| D>0 稳定域 H<4K | `smib_region_4K.kyx` | 符号 D,K | dI |
| D=K=1 渐近稳定（轨迹级） | `smib_asymptotic.kyx` | D=K=1 | dC + dI |
| 渐近稳定代数条件（仅代数） | `smib_asymptotic_parametric.kyx` | 符号 D,K,c | QE |
| D<0 能量增长（不稳定） | `smib_negdamping_unstable.kyx` | 符号 D<0,K | dI |
| Pm≠0 大信号能量不变 | `smib_tilted_largesignal.kyx` | 符号 D,K,Pm | dI |
| 带载平衡渐近稳定（仅代数） | `smib_loaded_equilibrium.kyx` | 符号 D,Ke | QE |
| Pm>K 失步发散（轨迹级） | `smib_loss_of_synchronism.kyx` | 符号 K,Pm | dC+dW+QE+dI |

### ✅ 参数化补全（本轮新增，11 个，全部 PROVED）

> 系统核实"固定实例 vs 参数化"状态后，将以下原本固定数值参数的已证结论推广为符号参数。
> 每个均经 KeYmaera X 5.1.2（Z3 后端）实跑 PROVED + sympy 精确 Lie 导数核验 + scipy 数值交叉验证（每个 ≥3 组参数）。

| 结论 | 新文件 | 参数范围 | 原固定实例 | 策略 |
|------|--------|---------|-----------|------|
| H<4K 亚水平集不变 | `stability_boundary_parametric.kyx` | 符号 D,K>0 | stability_boundary (D=K=1) | dI |
| 单机能量亚水平集不变 | `damped_oscillator_parametric.kyx` | 符号 K,D>0（Jn=1） | damped_oscillator (K=Jn=D=1) | dC+dW+QE / dI |
| D=0 能量精确守恒 | `exact_boundary_conservative_parametric.kyx` | 符号 K>0 | exact_boundary_conservative (K=1) | dI |
| LaSalle：偏离 ω 轴能量下降 | `lasalle_step2_parametric.kyx` | 符号 D1,D2,K>0 | lasalle_step2 (D1=D2=K=1) | dI |
| pH 能量平衡恒等式 h=H | `strict_dissipation_parametric.kyx` | 符号 D1,D2,K>0（J=1） | strict_dissipation (全 1) | dI |
| 鞍点截面失稳符号 | `saddle_instability_parametric.kyx` | 符号 D,K>0 | saddle_instability (D=K=1) | QE |
| H>4K 蕴含动能>0 | `exact_necessary_parametric.kyx` | 符号 K>0 | exact_necessary (K=1) | QE |
| ∀ε∃δ Lyapunov（H 度量） | `lyapunov_nonlinear_parametric.kyx` | 符号 D1,D2,K>0 | lyapunov_nonlinear (D=K=1) | existsR(δ=ε)+dI |
| ∀ε∃δ Lyapunov（单机） | `lyapunov_real_parametric.kyx` | 符号 D>0 | lyapunov_real (D=1) | existsR(δ=ε)+dI |
| 分量式稳定（能量分量<ε） | `component_stability_parametric.kyx` | 符号 D1,D2,K>0 | component_stability (D=K=1) | dC+dW+QE / dI |
| ∀ε∃δ Lyapunov（分量，witness δ=ε/(2K+2)） | `lyapunov_complete_parametric.kyx` | 符号 D1,D2,K>0 | lyapunov_complete (D=K=1) | existsR(项)+dC+dW+QE/dI |

**关键观察**：
- ∀ε∃δ 的 **H 度量**版本 witness δ=ε **与参数无关**（因 Ḣ≤0，H 不增）；
  **分量**版本 witness δ=ε/(2K+2) **依赖 K**，但可作为符号项直接喂给 `existsR`，故同样参数化（`lyapunov_complete_parametric.kyx`，witness 算术经 sympy 精确核验 sup H=ε）。
- Z3 后端无法 populate 有理式规范化派生引理（divideRat / ratForm* 等），符号惯量 J 的除法（K/J）类证明在本容器不可行；
  遵循 Conventions.md sec.4 将 J 归一化为 1，仅参数化阻尼/耦合 D、K。
- 参数化暴露并修正了一处隐含错误：`component_stability` 原结论 `1-c<ε` 仅在 K≥1/2 成立（由 H<ε 只能得 2K(1-c)<ε，即 1-c<ε/(2K)，K<1/2 时超过 ε）。
  参数化版本改用与参数无关的**能量分量**界 `2K(1-c)<ε`（数值在 K=0.3 处确认原结论会被违反）。

**审计结论（23 个固定实例文件的去向）**：
- **已参数化**：上表 9 个。
- **被 `parametric.kyx`（∀J,D,K>0）涵盖**，无需单独参数化：`dae_constraint.kyx`、`two_machine_nonlinear.kyx`（均为同一亚水平集不变性的实例）。
- **已有专门参数化伙伴**：`theorem_ph_bridge.kyx`↔`theorem_ph_bridge_parametric.kyx`、`smib_asymptotic.kyx`↔`smib_asymptotic_parametric.kyx`、`theorem_3machine.kyx`↔`theorem_3machine_linear.kyx`。
- **仍为实例级**：`asymptotic_d2_small.kyx`、`asymptotic_weak_coupling.kyx`、`parametric_asymptotic.kyx`（三者为有限时间渐近稳定 dC+dI，modified-Hamiltonian 系数 a 与时间界 C 需参数化 witness —— 即开放问题 C1）；`conjecture_neg_d2_lyapunov.kyx`（D₂<0 局部 x'Px，degree-4 Lie 导数 QE 在 Z3 后端实跑返回 SAT、产物 0 字节未闭合 —— 见"超时"节）。
- **线性化子系统**（`two_machine.kyx` 线性版、`dae_three_node.kyx`、`lyapunov_two_machine.kyx`）：可平凡参数化但研究价值低，暂留实例。

### ✅ 三机系统（线性拓扑 1-2-3，本会话补齐）

> 接手时三机只有 `theorem_3machine_linear`（线性化 pH，d<1/5）+ `theorem_3machine`（非线性实例，超时未验证）。补齐了两机有、三机缺的基础栈 + 失稳/必要性栈 + 环拓扑。**当前：15 个机器验证 (qed=1)，3 个开放（全部撞 Z3/SOS 后端墙）。** 链/环对照见下文四机节同款（三机环：`parametric_3machine_ring` ✅、`stability_boundary_3machine_ring` {H<8K} ✅，三角环最低鞍点 8K vs 链 4K）。

| 结论 | 文件 | 参数 | 状态 |
|------|------|------|------|
| 全无源亚水平集不变 | `parametric_3machine` | ∀D1,D2,D3,K>0 | ✅ dI (287ms) |
| ∀ε∃δ Lyapunov（H 度量，witness δ=ε） | `lyapunov_nonlinear_3machine` | ∀D1,D2,D3,K>0 | ✅ existsR+dI (405ms) |
| D=0 能量精确守恒 | `conservative_3machine` | ∀K>0 | ✅ dI (275ms) |
| 稳定域 {H<4K} 不变（吸引域） | `stability_boundary_3machine` | ∀D1,D2,D3,K>0 | ✅ dI (312ms) |
| 能量平衡恒等式 h=H | `strict_dissipation_3machine` | ∀D1,D2,D3,K>0 | ✅ dI (276ms) |
| ∀ε∃δ Lyapunov（分量，δ=ε/(4K+3)） | `lyapunov_complete_3machine` | ∀D1,D2,D3,K>0 | ✅ 除法消去 witness + 5 路 andR 拆分 QE (235ms)；负对照通过 |
| 失稳/必要性：D=0 越垒集 {H>4K} 正不变（能量势垒） | `saddle_instability_3machine` | ∀K>0 | ✅ dI；负对照(D>0)通过 |
| 失稳/必要性：δ₁≈π 处耦合力失稳（局部鞍点力符号） | `saddle_force_3machine` | ∀D₁,K>0 | ✅ **本会话新增** QE（与能垒版互补） |
| 失稳/必要性：K=0(带阻尼) ⟹ 永不达平衡、无同步 | `necessary_k0_3machine` | ∀D₁,D₂,D₃>0 | ✅ **本会话升级为强版**（守恒量 u₀≠0 + dC/dW/dI，镜像两机原版） |
| 失稳/必要性：D₁,D₂,D₃<0 ⟹ 能量单调增、不可能渐近稳定 | `necessary_dneg_3machine` | ∀D₁,D₂,D₃<0,K>0 | ✅ **本会话新增** dI；负对照(D>0)通过 |
| D₂<0 大信号下降 V̇≤0（仅 4 顶点 NSD） | `theorem_3machine_descent_parametric` | ∀d∈(0,3/20] | ✅ QE 4 顶点 (1.8s) |
| **D₂<0 大信号 box descent V̇≤0（整盒 c₁,c₂∈[4/5,1]）** | `theorem_3machine_boxdescent` | ∀d∈(0,3/20] | ✅ **本会话攻克**：抽象符号装配（V̇=4顶点凸组合）(114ms)；负对照通过 |
| D₂<0 大信号亚水平集不变 {V<1/25} | `theorem_3machine_invariant_parametric` | ∀d∈(0,3/20] | ❌ box descent 已证，但全 ODE 的 dI 装配 Z3 超时（5 种 tactic 均撞积式展开墙）；无有效 .kyp |
| 非线性实例 {V<1/25} 不变 (D₁=D₃=K=1, D₂=−3/20) | `theorem_3machine` | d=3/20 | ❌ 同上（全 ODE dI 超时）；无有效 .kyp |
| 渐近稳定（有限时间离开 {V≥target}） | `asymptotic_3machine` | D=K=1 | ❌ strict-decay 需 SOS 证书（与两机 asymptotic_closed 同墙）；无有效 .kyp |

**关键**：能量结构 Ḣ=−2ΣDᵢwᵢ²（sin 在线性拓扑上同样精确抵消）→ 全无源基础栈与两机持平。**D₂<0 这一侧本会话推进到 box descent 已机器验证**（`theorem_3machine_boxdescent`，qed=1）：核心观察是 V̇ 关于 (c₁,c₂) **可分仿射**（coeff(c₁c₂)=0，sympy 验证），故整盒上 V̇ 恰为 4 顶点值的**凸组合**（插值恒等式残差=0、权重和=1 均机器验证）；4 顶点 NSD 已证（descent 文件）；用**抽象符号装配引理**把 V̇ 作为"非负权×非正值之和"的见证（`lemma_sign_assembly`），Z3 只需逐项校验小目标，绕开使整盒 QE **爆内存**的 c·二次式乘积展开（已确认：即便把 4 顶点作为假设直接喂给整盒 QE 仍 OOM）。**仍未闭合**的是把 box descent 接到**全 10 变量 ODE 的 dI 不变性**：dIRule;chase 后与 box descent 桥接时 Z3 仍需把 chase 出的大多项式与 V̇ 归一化对消，撞同一堵积式展开墙（本会话试了 bare dI / dIRule+QE / chase+装配 / cut 全称 / cut 具体 五种结构，全超时或 OOM）。换 Mathematica/SOS 后端可破；如实记为开放项。`asymptotic_3machine` 的 strict-decay 是 Positivstellensatz/SOS 问题，与两机 `asymptotic_closed` 同墙。

**失稳/必要性栈（本会话补缺口）**：覆盖扫描发现两机有一整类 `necessary_*` / `saddle_*` 定理，三机一个都没有。补齐了能干净 dI/QE 的三条（均 qed=1、各带正阻尼负对照且负对照正确失败）：`saddle_instability_3machine`（D=0 越垒集 {H>4K} 正不变，与稳定域 {H<4K} 对偶）、`necessary_k0_3machine`（K=0 ⟹ 相对频率 w₁−w₂、w₂−w₃ 守恒，K>0 为同步必要条件）、`necessary_dneg_3machine`（全负阻尼 ⟹ H≥h₀ 能量单调增 ⟹ 不可能渐近稳定，∀D₁,D₂,D₃<0,K>0）。**未补** `necessary_d0` 类比：其诚实内容是能量守恒，已由 `conservative_3machine` 覆盖；一个朴素的"{动能>0} 不变"写法是**假命题**（动能在保守系统里振荡），KeYmaera X 正确拒绝，已弃而非硬凑。

### ✅ 四机系统：补全三机基础栈 + 拓扑相关性对照实验（本会话，链/环 10 PROVED + 1 conjecture；另 4 种拓扑见下节）

> 为分清"哪些结论与拓扑有关"，把系统扩到四机：(a) 把三机能干净 dL 移植的命题全部补到四机链；(b) **在两种拓扑上证同一条定理再对比**——链 1-2-3-4（3 条键）与环 1-2-3-4-1（4 条键 + 环流约束）。

| 结论 | 文件 | 状态 |
|------|------|------|
| 被动不变集 {H<1}（链） | `parametric_4machine` | ✅ dI |
| 被动不变集 {H<1}（环） | `parametric_4machine_ring` | ✅ dI（与链同一行，环多一条键项） |
| D=0 能量守恒 | `conservative_4machine` | ✅ dI |
| ∀ε∃δ Lyapunov（H 度量） | `lyapunov_nonlinear_4machine` | ✅ existsR+dI |
| 能量平衡恒等式 h=H | `strict_dissipation_4machine` | ✅ dI |
| 稳定域（链） | `stability_boundary_4machine` {H<4K} | ✅ dI（阈值见诚实标注） |
| 稳定域（环） | `stability_boundary_4machine_ring` {H<8K} | ✅ dI（环最低鞍点 8K，数值） |
| 失稳：D=0 越垒集 {H>4K} | `saddle_instability_4machine` | ✅ dI |
| 失稳：鞍点力符号 | `saddle_force_4machine` | ✅ QE |
| 必要性：K=0(带阻尼) 永不平衡 | `necessary_k0_4machine` | ✅ dC/dW/dI（强版） |
| 必要性：全负阻尼能量增 | `necessary_dneg_4machine` | ✅ dI |
| **分量 ∀ε∃δ Lyapunov** | `lyapunov_complete_4machine` | ❌ **conjecture**：14 变量 QE，OOM(-Xmx4g)/超时(-Xmx10g,600s)；数学对(witness δ=eps/(6K+4)，sympy 确认)，无有效 .kyp |

**结论分档**：
- **与拓扑无关（被动栈 + 必要性/失稳）**：链和环用**完全相同的一行 dI** 都闭合，因为 Ḣ=−2ΣDᵢwᵢ² 对任意反对称耦合都成立（sin 总抵消）。链+环这一对（被动不变集 + 稳定域）是拓扑无关性的直接实证；三机也补了环对照（见三机节）。
- **与拓扑相关（仅数值阈值）**：稳定域 {H<c} 的 dI 对任意 c 成立（形式上拓扑无关），但能垒值是数值的：链 4K vs 环 8K（环流约束禁"单键到 π"，fsolve 实测）。
- **与拓扑强相关（D₂<0 非被动 Lyapunov 设计）**：`theorem_3machine_boxdescent` 的可分仿射性（无 c₁c₂ 交叉项）是**链拓扑指纹**——环上首尾键耦合 ⟹ 出现交叉项 ⟹ 4 顶点凸组合失效。这类需为每种拓扑重设计，未扩四机（有据，非遗漏）。
- **唯一被动栈缺口**：四机分量 ε-δ（`lyapunov_complete_4machine`）——三机(10 变量)能过，四机(14 变量)撞 QE 维度墙。本会话做了 3 次有原则的攻坚（全 hide 圆约束 / 选择性 hide / 加资源），诊断确认每个分量都真需要全部圆约束（`w_i²≤H` 依赖 cⱼ≤1），故 hide 破坏正确性——纯维度墙，维持 conjecture。

### ✅ 四机拓扑空间穷举完全（本会话，6 种同构类全覆盖）

> 4 节点连通图共 **6 种**同构类（穷举去重）。每种证 **被动不变集 {H<1} + 稳定域 {H<能垒}**，全部 qed=1。开证前每种拓扑的 pH 编码都用 sympy 独立核验 Ḣ=−2ΣDᵢwᵢ²（sin 抵消，确认键定向正确）；提交后机械核验关联矩阵反对称 + 度序列。

| # | 拓扑 | 键数 | 度序列 | 被动 {H<1} | 稳定域能垒 |
|---|------|------|--------|-----------|-----------|
| 1 | 链 path | 3 | (1,1,2,2) | `parametric_4machine` ✅ | `stability_boundary_4machine` 4K |
| 2 | 星 star/claw | 3 | (1,1,1,3) | `parametric_4machine_star` ✅ | `..._star` 4K |
| 3 | paw（三角+尾） | 4 | (1,2,2,3) | `parametric_4machine_paw` ✅ | `..._paw` 4K |
| 4 | 环 cycle | 4 | (2,2,2,2) | `parametric_4machine_ring` ✅ | `..._ring` 8K |
| 5 | 菱形 diamond（K4−1边） | 5 | (2,2,3,3) | `parametric_4machine_diamond` ✅ | `..._diamond` 8K |
| 6 | K4 完全图 | 6 | (3,3,3,3) | `parametric_4machine_k4` ✅ | `..._k4` 12K |

**两个干净结论**：
1. **被动栈拓扑无关性 = 全覆盖实证**（不再是链/环两点外推）：全部 6 种拓扑（含多环的菱形、K4）用**完全相同的一行 dI** 闭合。Ḣ=−2ΣDᵢwᵢ² 对任意反对称关联都成立。
2. **能垒值是唯一随拓扑变的量，且单调于连通度**：树/含叶子键（链/星/paw）= **4K**（叶子键可单独翻 π）；单/双环（环/菱形）= **8K**（环流约束禁单键翻转）；完全图 K4 = **12K**（最密）。连得越密 → 同步井越深。（诚实标注：dI 形式只证"{H<c} 任意 c 不变"，能垒是 fsolve 数值最低鞍点，非形式紧界。）
3. **穷举仅限拓扑无关的被动栈 + 稳定域**；D₂<0 非被动设计仍只有链（强拓扑相关，需逐图重设计，非机械可推广）。

### ⚠️ 复验检查与诚实性修正（本会话末，重要）

对本会话全部 11 个新增文件做了 **fresh 重跑**（串行，写 /tmp）：11/11 的 fresh qed 与仓库 .kyp 完全一致，**0 空壳、0 并行污染**。

但**对抗测试暴露了一处必须修正的表述越界**（KeYmaera X 协议第 3 条："形式证 ≠ 自然语言声称"）：
- 把链稳定域阈值改成 8K（`chain@8K`）→ **仍 PROVED**；把环的改成 4K（`ring@4K`）→ **仍 PROVED**。
- **原因**：dI 证 {H<c} 不变只用了"H 单调不增"，对**任意** c>0 都成立。所以 **4K（链）vs 8K（环）的能垒区别根本不在这些形式证明里**——形式证明只说了"某个亚水平集不变"（任意阈值）。
- **4K/8K 作为最低逃逸鞍点是数值结论**（sympy/fsolve：链最低鞍点 4K；环因环流约束禁止"单键到 π"，最低鞍点 8K）。
- **已修正**：`stability_boundary_{3,4}machine`、`_4machine_ring`、`saddle_instability_3machine` 四个文件头注释，明确区分"形式证明了 {H<c} 不变" vs "紧性/ROA/能垒 = 数值结论，不在 .kyx 内"。证明本身未动（qed=1 复验通过），仅改注释。

这条同样适用于早先的 2/3 机稳定域：它们的形式内容都是"{H<4K} 是**某个**正不变集"，不是"4K 是**最大**不变域/吸引域边界"。后者是数值的。

### 全量复验（本会话，KeYmaera X 5.1.2 + Z3）

对全部 55 个两机文件做了全量实跑复验（产物写 /tmp，不改动仓库 `.kyp`）。结论：

- **47 个 PROVED**（fresh `\qed`）：45 个秒过 + `parametric_asymptotic`（qe≈124s，重但可证）+ 修复后的 `exact_necessary`。45 个已提交产物全部有效（0 空壳）。
- **修复 2 个空壳/偏差文件**：`impossibility_ph_linear`（之前提交的 `.kyp` 是 0 字节空壳 → 补真证明）；`exact_necessary`（bare `QE` 未展开 `K=1` 定义而 deviate → 改 `expandAllDefs; QE`）。
- **8 个未闭合**（下两节）。

### ⚠️ Tactic 已写但 KeYmaera X 未闭合（NOT 机器验证，6 个）

| 结论 | 文件 | 未闭合原因（Z3 实测） |
|------|------|---------|
| D₂<0 局部 x'Px 渐近稳定 | `conjecture_neg_d2_lyapunov.kyx` | **本会话诊断+修复**：原 tactic 不健全——演化域缺局部界 V≤1，子目标对大状态为假（max V'+V/400=+62.96 @ V≈60），故 Z3 返 SAT（非单纯超时）。加 V≤1 后子目标变真（max=−0.0007）；但闭合需 S-procedure/SOS（"球{V≤1}∩簇{s²+c²=1} 上二次型≤0"），Z3 nlsat 不行（Mathematica 可）。命题本身真（轨迹验证渐近稳定） |
| 弱阻尼渐近稳定 (D₂=1/10) | `asymptotic_d2_small.kyx` | 脏有理数 a=1/14，QE 超时 |
| 弱耦合渐近稳定 (K=1/10) | `asymptotic_weak_coupling.kyx` | 脏有理数，QE 超时 |
| pH gap 参数化 (∀d) | `gap_parametric.kyx` | 薄裕度 ∀d QE 超时 |
| Level C 多项式正定（单体） | `theorem_levelC_polynomial.kyx` | **本会话拆解**：拆成 3 个子式后 M1>0✓(86ms)、M3=det✓(9.1s) 单独已证（`theorem_levelC_M1/M3.kyx`，带 .kyp）；M2 单体两形式均超时，但有 q-幂全正证书（`theorem_levelC_M2.kyx`，Routh 参数化下每个 q 幂系数全非负 ⟹ 正单项式之和）。整体 = 2/3 机器验证 + 1/3 结构证书 |
| sin² 必需性参数化 (∀b,d) | `impossibility_parametric.kyx` | 量词交替 + 薄裕度，QE 未闭合 |

（另：三机 `theorem_3machine.kyx` 同属未闭合，5×5 dI / 9 变量 QE 超时 —— 非两机，单列。）

这些的 Lie 导数代数已手工+数值核验为真，仅 KeYmaera X 的 QE（Z3/CAD）在本后端跑不完。

### 仍是猜想（有 Problem 无 Tactic）

| 猜想 | 文件 | 核心困难 |
|------|------|---------|
| C1. 一般参数渐近稳定 | `conjecture_parametric_asymptotic.kyx` | existsR 需参数化 witness |
| C2. Routh 边界外不稳定 | `conjecture_instability_boundary.kyx` | 菱形模态需 dG 构造逃逸轨迹 |

### 关键认知：QE 可处理性

**低次多项式 dI 秒过；高次/大矩阵/脏有理数/量词交替超时。**
- theorem_ph_bridge（degree-2/3 dI）：344ms ✓
- impossibility 原 ∀∃ 形式：超时 → 重写为纯 ∀ Sylvester 析取：通过 ✓
- 三机 5×5 dI、x'Px degree-4：超时 ✗

教训：形式化成功与否高度依赖**问题的代数复杂度和表述方式**，不只是命题真假。

---

## 方法论认知

1. **形式化验证（KeYmaera X）对全无源 pH 系统非常有效**。dI + dC + QE 可以自动证明 Lyapunov 和渐近稳定性。微分不变量绕过了 ODE 解理论。

2. **pH 结构的真正价值是代数简化**：sin 项的精确抵消将非线性能量分析化简为二次型问题。但这不等于稳定性——二次型不定时需要额外工具。

3. **交叉验证是必需的**。每一个未经验证的结论都有可能是错的。这次发现的错误包括：符号搞反、公式只对特定参数正确、仿真时间不足造成假象。

4. **参数特化 vs 一般性是实际瓶颈**。KeYmaera X 的 existsR 策略需要显式 witness，当 witness 依赖符号参数时（如 δ=ε/(2+2K)），证明可能需要手工参数化。渐近稳定性的修正 Hamiltonian 系数和时间界都依赖参数，导致一般性证明困难。

5. **"难点在哪"这个问题本身需要不断修正**。从最初的"10个障碍"到最后的"1个核心问题"，每一轮推敲都排除了假问题或发现了新问题。当前的认知仍可能有错。
