# GFL-VSC 风险机制的参数化证书(R1 / R2 / R3)

> 三类结构性失稳机制的参数化分析:**R1** 弱网电气模 onset、**R2** 同步平衡消失、
> **R3** 同步吸引域 vs PLL 阻尼。`kyx/` 是 KeYmaera X 5.1.2(自带 z3)证书,
> `numerical/` 是支撑数值,`results/` 是证明日志。
>
> **2026.06 修订(按形式化评审):** 评审正确判定原 R1 三条是 tautology、R3 多条把仿真数
> 塞进 dL 前提或把 2D 同步核冒名 10D。已据此**降级/重做/改名**,见下表与"评审修订"节。
> 真成果是 **R2**(folded 折叠 + Σ₂ 闭式);R1 退回 **conjecture(待证)**;R3 明确标"约化核"。

## 状态总览(修订后)

| 文件 | entry | 状态 | 内容 / scope |
|------|-------|------|------|
| `kyx/conjecture_R1_electrical_onset.kyx` | 1 | **conjecture(无 tactic,待证)** | R1 退回待证:真目标是 Δ₇(p) 多项式 sign chart,CAS 超时,未做 |
| `kyx/R2_fold.kyx` | 4 | proved | fold 根计数(\|M\|≷Vg)/ **node-saddle 由 arcsin 几何导**(修订)/ Wu 恒等改写(改名) |
| `kyx/R2_sigma2_symbolic.kyx` | 2 | proved | **Σ₂ 全 6 参数闭式** Φ(p)（真成果) |
| `kyx/R3a_energy_barrier.kyx` | 3 | proved(**2D 核**) | 能量屏障 Vdot=−b·dw²;标题已标"REDUCED 2D CORE not 10D" |
| `kyx/R3_basin.kyx` | 4 | proved(**2D 核**) | 不变性原理(去掉 toy ODE)/ 鞍点排除 / **结构单调(IFT 式,非拟合斜率)** / 阈值 |
| `kyx/R3note_decoupling.kyx` | 3 | proved（**重做,非 vacuous**） | l₁<0 局部法形无逃逸 / LOS 由 R2 鞍点裕度支配 / 裕度独立于 l₁。对抗检验:l₁>0 变体证不出 |
| **proved 合计** | **16** | | R1 的 1 条是 conjecture,不计入 proved |

复现:`cd kyx && java -jar <keymaerax.jar> -prove <file>.kyx -tool z3`
(**必须用 KeYmaera X 自带 z3,不要 `-z3path` 外部 z3** — 外部会挂启动期公理推导);
`cd numerical && python3 risk_numerical.py`(需 numpy/sympy/scipy)。

## 评审修订(逐条)

- **R1 → conjecture**:原 3 条(D8=a8·D7→D8=0、∃W2=W、m·cs>0→>0)是恒等/代入,
  把仿真数 +644 塞进前提。已退回 `conjecture_R1_electrical_onset.kyx`(Problem-only,
  无 tactic),文件头写明真目标(Liénard–Chipart 等价、Δ₇(p) 参数面、谱微扰横截性)
  和工具路线(Maple/Mathematica/Sage Gröbner 求 sign chart)。**不再占用 proved 名义。**
- **R2·3 重做**:node/saddle 异号不再手取 C2=−C1,改从 θ₁=arcsin(M/Vg)、θ₂=π−θ₁ 的
  几何(cos(π−t)=−cos t)导出。新 entry "node-saddle from geometry"。
- **R2·4 改名**:原"经典极限"实为恒等改写(未做 Cf→0 极限,因没建有限-Cf fold)。
  改名"identity rewrite",注释明示这是代数同一面、**非极限证明**。
- **R3a 改 scope 标签**:标题加"REDUCED 2D CORE not 10D",注释说明 ∇V 链式法则手做、
  10D SOS 未完成。
- **R3·1 toy ODE 删除**:原 V'=−V 与模型无关。改为抽象不变性原理(V≤c ∧ dV≤0 → V+dV≤c),
  真实流不变性由 R3a 的 Vdot=−b·dw² 提供。
- **R3·3 重做**:单调性不再靠拟合斜率 k>0,改从结构 Vdot=−b·dw²(b 的线性单调)导
  "b₂>b₁ ⟹ 逐点耗散更大 ⟹ 认证 level 不减"。
- **R3·2/·4 标注**:c*=3.098、V_saddle=62.98 等明确标为**数值输入**,dL 只证代数蕴含。
- **R3-note → 重做为 proved(非 vacuous)**:原 2 条是 vacuous 独立实数。评审给的见证
  Kp=0.50,Ki=400 我**复现不出 l₁<0**(实测 l₁=+1.4e-6),所以不照搬。改走**结构论证**
  (`R3note_decoupling.kyx`,3 条):normal-form 推理表明 **l₁<0 的局部 Hopf 径向法形
  `r'=a·μ·r+l₁·r³` 在稳定侧无有限幅逃逸**(单凭 l₁<0 不致 finite-kick LOS),而失同步由
  **R2 鞍点裕度 Vg²−M²** 支配(可任意小),依赖 (M,Vg) **不依赖 l₁** ⟹ sign l₁ 非判据。
  对抗检验:把 l₁<0 改 l₁>0,local 那条 KeYmaera X **证不出**(非平凡)。
- **R1 部分进展(CAS,非 dL)**:`numerical/R1_sign_chart.py` 真算出 **Δ₇(g,K_ad) 显式双变量
  多项式**(total degree 20, 143 项),并描出 sign chart Lg\*(K_ad)、Liénard–Chipart
  (D1..6>0、D7 定边界)、从真 Δ₇ 取的横截性符号。这是评审要的真多项式 + sign chart。
  **仍 open**:全 8 参数符号 Δ₇(CAS 超时)、dL 侧证明(degree-20 双变量 Hurwitz 非 QE 能力)。
  故 R1 dL 文件保留 `conjecture_`,真内容在 CAS 脚本。

## 仍未做到 / 待证(明示)

- **R1 全符号 + dL 证明**:Δ₇ 双变量(Lg,K_ad)已算出并描了 sign chart(`R1_sign_chart.py`),
  但 **全 8 参数符号 Δ₇ CAS 超时**;且 degree-20 双变量 Hurwitz 符号分析**非 dL/QE 能力**,
  故 dL 侧仍 `conjecture_`。真内容在 CAS 脚本,不是 dL 定理。
- **10D 全状态屏障**:全非线性 SOS 未完成(求解器装不上;手搭 SOS 对核 infeasible,
  查实因是误用的交叉项 V 非 Lyapunov 函数);现有 R3a/R3_basin 是**2D 约化核**。
- **R3-note 的"全局 LOS"严格化**:结构论证(normal-form + 鞍点裕度)已 proved,但完整的
  **10D nonlinear kick → LOS 时域证书**未做(需重建 10D 非线性场积分,`sweep.py` 只暴露 Jacobian)。
- **R2·4 的 Cf→0 极限**:未建有限-Cf fold,故未做极限证明(现为恒等改写)。

## R1 — 弱网使电气模过虚轴(onset)

- **机制**:变流器-滤波器-线路阻抗谐振失阻尼,**非** PLL 分岔。
- **Σ₁ 交付**:8 状态 PLL-冻结电气子系统 A_e 的 Routh 行列式 **Δ₇(g)=0**(g=1/Lg),
  数值上是 **degree-13 多项式**,正实根隔离出 onset。
- **数值确认**(`risk_numerical.py`):onset 两点 Re λ≈0(−6e-13、+1.6e-12,真虚轴穿越);
  物理 onset `Lg*=0.00484 H` 处 **ω₀=75.15 rad/s(12 Hz)≠ ω_LCL=3473 rad/s(553 Hz)**;
  横截性 **dRe λ/dLg=+644>0**(弱网入 RHP)。
- **证书** `R1_routh.kyx`:Routh onset 签名(Δ₇=0 边界 + Δ₈=a₈Δ₇)、虚轴穿越存在性、
  横截性符号(先实测 +644 再写,改掉过一处一开始写反的符号)。

## R2 — 同步平衡消失(鞍结/折叠)

- **机制**:不平衡力矩 M=id_ref·wn·Lg+iq_ref·Rg 超过 Vg ⟹ 无同步平衡 ⟹ θ 无界失同步。
- **Σ₂ 全符号闭式**(标量问题,不超时,与 R1 的 8×8 不同):
  `Φ(p) = Lg²·id_ref²·wn² + 2·Lg·Rg·id_ref·iq_ref·wn + Rg²·iq_ref² − Vg²`,
  Φ<0 两平衡(node+saddle),Φ>0 零平衡;经典极限退化到 Wu 边界 |M|=Vg。
- **证书** `R2_fold.kyx`(4)+ `R2_sigma2_symbolic.kyx`(2)。

## R3 — 同步吸引域 vs PLL 阻尼

- **R3-pre(边界类型)**:吸引域边界 = **R2 鞍点的稳定流形**(数值 V_saddle=63 ≫ c*),
  不是极限环、不是同宿。
- **R3a(屏障证书)**:用**倾斜摆能量** `V=½dw²+K(cosδ*−cosδ)−Pm(δ−δ*)`,实算
  **Vdot=−b·dw² 精确**(误差 7e-17);LaSalle ⟹ {V<c*} 内估吸引域,c*=V(saddle)。
  这是精确多项式-三角恒等式,**不需要 SOS 求解器**,直接 QE 证。`R3a_energy_barrier.kyx`(3)。
- **R3b(单调性)**:c*(PLL 阻尼) 数值单调递增(0.05→2.41 … 0.40→5.18);
  阈值面 Σ₃={c*=0}。`R3_basin.kyx`(4)。
- **R3-note(否定结论)**:**sign l₁ 不是失同步判据**。数值开集:固定控制 Kp=0.8,Ki=150
  (l₁<0,Bautin 读法"安全"),SCR=0.40、id_ref∈{120,160} 时 **l₁<0 且 |M|/Vg>1**
  (已过 fold,全局失同步)。l₁ 管局部 Hopf(Σ₁),失同步管 fold(Σ₂),代数独立。
  `R3note_l1_not_criterion.kyx`(2)。

## 诚实边界(务必知道)

1. **dL/QE 不是线性代数/分析包**。证书证的是各机制**归约到的代数命题**(Routh 签名、
   fold 不等式、能量恒等式、单调蕴含),不是完整 8×8 符号谱或全局吸引域。完整 Δ₇(g)
   deg-13、特征值、Schur 等在 `numerical/` 的 sympy/numpy 层。
2. **Σ₁ 没有全符号闭式**:8×8 符号行列式即使部分符号也重,全 8 参数实测多次**超时**——
   这是 CAS 在高维符号行列式上的真实天花板,不是方法问题。交付的是沿分岔方向(Lg)的
   显式 Δ₇(g) 多项式面。Σ₂(标量)则做到了全符号闭式。
3. **R3a 是约化同步核 + 内估**,不是 10D 全状态严格吸引域。
   - **10D 全非线性 SOS 没做到**:`SumOfSquares`/picos 装不上;手搭 cvxpy SOS 对同步核
     **infeasible**(查实因:误用的交叉项 V 根本不是 Lyapunov 函数,1424 处 Vdot>0,
     SOS 正确拒绝证伪)。改用能量法绕过,得到的是**约化核**的严格屏障。
   - 10D **线性** Lyapunov 盆需 balancing 预处理才解得动(裸 SCS 在 cond=2.2e5 下失败);
     这条没单独落成证书,仅记录于此。
4. **R1 横截性 / R3b 单调性**的证书证的是**符号代数蕴含**(正×正=正、仿射单调),
   其中的数值斜率(+644、k>0)来自数值扫描,是前提不是结论的一部分,已在证书注释标明。
5. 这些是**参数化失稳机制的代数骨架**,适合作工程稳定边界的形式化锚点;**不**等价于
   "已严格证明该 10D 系统在某区域全局稳定"。

## 关于 l₁(与 `numerical/` 的关系)

R3-note 用到的 l₁(第一 Lyapunov 系数)来自 `formalization/numerical/sweep.py` 的弱网
Hopf 管线(另一条线)。R3-note 的要点正是:**那条线的 l₁ 符号不能用来判全局失同步** —
这也是为什么本目录的 R3 改用 R2-fold + 能量屏障而非 Bautin/l₁ 框架。
