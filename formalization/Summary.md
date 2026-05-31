# 电力电子化电力系统的形式化：已验证的认知

> 2026.05 | 只包含经过验证的结论和诚实的未知

---

## GFL-VSC 慢频率模式（Lean 4 + Mathlib，机器已验证）

> 功率锁定跟网变流器（GFL-VSC）的慢频率模式形式化。完整说明见 [`gfl/README.md`](gfl/README.md)；
> 源在 `gfl/GFL/*.lean`，公理审计见 `gfl/GFL/Audit.lean`，数值交叉验证见 `gfl/validate.py`。

**结论**：电流控制、功率锁定的 GFL-VSC，其慢频率（电网频率）模式是**纯实数衰减模**，特征值
`−D/(2H)`；当且仅当显式存在角度→功率耦合 `Ks` 且 `β·Ks > b²/4`（`β:=wn/(2H)`）时才转为振荡。
裸 GFL 因 Power Lock（引理 0）强制同步系数 `K=0`（即 `Ks=0`），其频率模式只衰减、永不振荡。

**机器已验证（`lake build`，无 `sorry`，公理仅 `[propext, Classical.choice, Quot.sound]`）**：

| 结论 | Lean 名 | 文件 |
|------|---------|------|
| 引理 0（Power Lock，命门，纯代数）`e_P=0 ⟹ i_d=P_ref/(1.5Vg)` | `powerLock` | `gfl/GFL/Model.lean` |
| 推论 0a `i_d*` 恒定 ⟹ `K=0` | `syncCoeff_zero` | `gfl/GFL/Model.lean` |
| 定理 A（Variant U 零特征值，`e₉` 左特征向量，`det=0`） | `variantU_zero_eigenvalue` | `gfl/GFL/TheoremA.lean` |
| 定理 B（约化系统**精确** `dw'=−b·dw`，`λ_slow=−D/(2H)`） | `reduced_exact` | `gfl/GFL/TheoremB.lean` |
| 定理 B（全系统 Schur 项 `ρᵀA⁻¹c=κK=0` 精确） | `schur_term_zero` | `gfl/GFL/TheoremB.lean` |
| 定理 C（伴随矩阵特征多项式 `λ²+bλ+βKs`） | `charpoly_eq` | `gfl/GFL/TheoremC.lean` |
| 定理 C1（`Ks=0` ⟹ 根 `{0,−b}` 全实） | `thmC_Ks_zero` | `gfl/GFL/TheoremC.lean` |
| 定理 C2（`Ks>0` ⟹ `−b/2±iω`，振荡 ⟺ `βKs>b²/4`，`ω_osc=√(βKs−b²/4)`） | `thmC_onset` | `gfl/GFL/TheoremC.lean` |

**三个命门的诚实处理**：(1) 引理 0 先证、纯代数；(2) 定理 B 区分"约化精确 / 全系统 O(ε²)"——只证
约化场精确 `−b·dw` 与 O(1) Schur 项精确为 0，**不**声称全 9×9 系统精确 `−D/(2H)`；(3) 定理 C 用
`β:=wn/(2H)` 与题设一致。建模忠实性：内场 `F_inner` 抽象承载（只用到 `F7=e_P`），§6 雅可比块结构按
题目"by inspection"给定为前提，定理 B 的 `A·v=−c`（IFT 微分）与 `v₀=0`（推论 0a）为前提，其余全部从
头证明。`validate.py` 在**完整 §3–§4 非线性 9 态模型**上独立复现 §9 全部数值锚点（`i_d*=80` 恒定、
Variant U 恰一个零特征值、`λ_slow≈−D/2H`、Schur 项 `2.9e-19`、定理 C 起振频率 `0.089/0.199/0.399/0.892 Hz`）。

> 注：本节是 Lean 代数/谱证明（与下文 pH-DAE 的 KeYmaera X 动力学证明互补、彼此独立）。Mathlib olean
> 缓存在本环境不可达，故 Mathlib 由源码编译（toolchain `v4.31.0-rc1`，依赖 pin 在 `lake-manifest.json`）。

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

**大信号 + 参数化的补足（`theorem_ph_bridge_parametric.kyx`）**：以上参数化证明全部在 c=cosδ=1 处取值，即**线性化**于平衡点；`theorem_ph_bridge.kyx` 的非线性大信号不变性又只证了**固定实例** d=3/10。缺的一块是"大信号 ∧ 参数化"。关键结构：V̇=x′M(c)x，M(c) **关于 c 仿射**，故在 c∈[4/5,1] 上 V̇ 是两端点的凸组合 → V̇≤0 在整段大信号域上 ⟺ 两端点 V̇≤0。本文件用纯全称 QE 证明 ∀d∈(0,2/5]，c=1 与 c=4/5 两端点的二次型均负半定（Lie 导数已独立用 sympy 从 V 与 ODE 重算核验，两端点恰为 6V̇|₍c=1₎ 与 30V̇|₍c=4/5₎）；再由仿射凸组合（一行恒等式）得 V̇≤0 在 c∈[4/5,1] 整段大信号域上、对全部 d∈(0,2/5] 成立。2/5=Routh 边界(d<1)的 40%（此固定闭式证书在 c≥4/5 上的精确上限是 d≈0.441）。注：完整的 box 不变性 [ODE]V<bound 在符号 d 下 dI 仍超时（5 变量 QE），故大信号"下降"是参数化的，大信号"亚水平集不变"仍是固定实例。

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

### ✅ 机器已验证 PROVED（13 个）

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

### ⚠️ Tactic 已写但 QE 超时（NOT 机器验证，4 个）

| 结论 | 文件 | 超时原因 |
|------|------|---------|
| 三机 pH Lyapunov | `theorem_3machine.kyx` | 5×5 dI，9 变量，QE >350s |
| D₂<0 局部 x'Px 渐近稳定 | `conjecture_neg_d2_lyapunov.kyx` | 4 次多项式 + s²+c²=1，QE >350s |
| 弱阻尼渐近稳定 (D₂=1/10) | `asymptotic_d2_small.kyx` | 脏有理数 a=1/14，QE >200s |
| 弱耦合渐近稳定 (K=1/10) | `asymptotic_weak_coupling.kyx` | 脏有理数，QE >200s |

这些的 Lie 导数代数已手工+数值核验，但 KeYmaera X 的 QE（基于 Z3/CAD）跑不完。

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
