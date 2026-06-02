# 风险机制的参数化证书(R2 已改对锚定真模型;R1 撤回;R3 标经典摆)

> **2026.06 模型审计 + 改对(按 R1 同标准把 R1/R2/R3 全查了一遍,并把能改对的改对):**
>
> - **R1 — 撤回**:8×8 电气 A_e 是手编矩阵;且经真模型检验,弱网失稳是 PLL 模、无电气 onset。
>   见 `R1_RETRACTED.md` + `numerical/R1_real_model_test.py`。**机制不存在,无可改,永久撤回。**
> - **R2 — ✅ 已改对**:经典 `|M|=Vg` 不是真 fold。**已在真模型 sweep.py 上重做**:真失平衡是
>   vcd 平衡二次的**鞍结 disc=0**(系数全真),`kyx/R2real_fold.kyx`(5 条全 proved)+ 3 组数值验证
>   (`numerical/R2real_validate.py`,与 sweep.py 的 `pv()` 崩溃边界逐点吻合)。真 fold 在 SCR\*≈0.370,
>   比 PLL Hopf(SCR_H≈0.905)更深。旧经典 `|M|=Vg` 降为对照。
> - **R3 — 经典摆(未改)**:swing 核 `δ'=dw, dw'=−b·dw−K·sinδ+Pm` **不在任何提交模型里**(§12 无
>   swing/惯量,§13 有 swing 但无 sinδ/角态)。是 textbook 同步机摆方程。真 GFL 的 10D 非线性吸引域
>   是另一个更难的问题(见"仍未做到");现 R3 仅作经典摆参照。
>
> 真 GFL 的弱网**失稳**(非 fold)在 `numerical/`、`freq_mode/`(PLL 模 Hopf,SCR_H≈0.905,l₁)。

## 状态总览(审计 + 改对后)

| 文件 | entry | KeYmaera X | scope |
|------|-------|-----------|------|
| `R1_RETRACTED.md` | — | **撤回** | 手编模型 + 真模型检验机制不存在 |
| `kyx/R2real_fold.kyx` | 5 | **proved** | ✅ **真模型** sweep.py 鞍结 fold disc=0(系数全真,3 组数值验证) |
| `kyx/R2_fold.kyx` | 4 | proved | 经典摆对照;\|M\|=Vg 非真 fold(降级) |
| `kyx/R2_sigma2_symbolic.kyx` | 2 | proved | 经典摆 Σ₂ 闭式(对照,scope=Wu 边界) |
| `kyx/R3a_energy_barrier.kyx` | 3 | proved | 经典摆能量屏障 Vdot=−b·dw²(2D 核) |
| `kyx/R3_basin.kyx` | 4 | proved | 经典摆吸引域:不变性/鞍点排除/单调/阈值 |
| `kyx/R3note_decoupling.kyx` | 3 | proved | l₁(局部)vs 鞍点裕度(全局)解耦;非 vacuous |
| **proved 合计** | **21** | | R2real(5,真模型)+ 经典摆对照(16) |

复现:`cd kyx && java -jar <keymaerax.jar> -prove <file>.kyx -tool z3`
(**必须用 KeYmaera X 自带 z3,不要 `-z3path` 外部 z3** — 外部会挂启动期公理推导);
`cd numerical && python3 risk_numerical.py`(需 numpy/sympy/scipy)。

## 评审修订(逐条)

- **R1 → 撤回(造模型错误)**:不只是 tautology——更根本的问题是 R1 的 8×8 A_e 是**手编
  矩阵**,不是仓库任何真实模型。原 3 条恒等 tautology(D8=a8·D7→D8=0 等)+ 后来基于该假
  矩阵的 Δ₇ sign chart **全部删除**,见 `R1_RETRACTED.md`。若重做须从 `sweep.py` 真 10 状态
  f 导出真 A_e。
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

## 仍未做到 / 待证(明示)

- **R1 整块(撤回,且经真模型检验机制不存在)**:已用 `sweep.py` 真 10 状态 f 正确导出
  电气块 A_e(`numerical/R1_real_model_test.py`)。结论:(a) dq 镜像在有载平衡点破坏
  (dev=94),空间相量 8→4 复约化**不适用**真模型;(b) 真 A_e 在弱网全程牢稳(maxRe≈−100,
  从不过零),而全 10D 在 SCR≈0.905 失稳 ⟹ **弱网失稳是 PLL/耦合模,不是电气 onset**。
  R1 的前提对本模型为假——**没有"电气 onset Σ₁"可证**。真弱网失稳由 `numerical/`、
  `freq_mode/` 那条 PLL-模 Hopf 线(SCR_H≈0.905、l₁)覆盖。R1 永久撤回,不是待重做。
- **10D 全状态屏障**:全非线性 SOS 未完成(求解器装不上;手搭 SOS 对核 infeasible,
  查实因是误用的交叉项 V 非 Lyapunov 函数);现有 R3a/R3_basin 是**2D 约化核**。
- **R3-note 的"全局 LOS"严格化**:结构论证(normal-form + 鞍点裕度)已 proved,但完整的
  **10D nonlinear kick → LOS 时域证书**未做(需重建 10D 非线性场积分,`sweep.py` 只暴露 Jacobian)。
- **R2·4 的 Cf→0 极限**:未建有限-Cf fold,故未做极限证明(现为恒等改写)。

## R1 — 撤回

见 `R1_RETRACTED.md`。R1 的 8×8 电气 A_e 是手编矩阵、非真实模型,全部产物已删除,
不占成果位。当前**无 R1 成果**。

## R2 — 同步平衡消失(鞍结/折叠)

### ✅ R2-real(已改对,锚定真模型 sweep.py / §12)—— `kyx/R2real_fold.kyx`(5,全 proved)

真模型的失平衡机制是 **vcd 平衡二次方程的鞍结(电压崩溃)**,不是经典 `|M|=Vg`。从 sweep.py
平衡 `cos²+sin²=1` 推出真二次 `a2·vcd²+a1·vcd+a0=0`,**系数全是真系数**:
- `a2 = (1−wn²·Lg·Cf)² + (Rg·wn·Cf)²`(=al²+be²),`a1 = −2·Rg·idr`,`a0 = Lg²·idr²·wn² + Rg²·idr² − Vg²`
- 真 fold = 判别式 `disc = a1²−4·a2·a0 = 0`

证书 5 条(KeYmaera X 全 proved):(1) a2>0 是真二次;(2) **disc=0 ⟹ 重根**(鞍结点);
(3) **disc>0 ⟹ 两不同平衡**(node+saddle,witness s²=disc);(4) **disc<0 ⟹ 处处>0 无平衡**(崩溃,
即 `pv()` 返回 None 的分支);(5) **绑定**:抽象 disc = 真物理 fold 多项式 disc(wn,Vg,Rg,Lg,Cf,idr)。

- **定位**:真 fold 在 **SCR\*≈0.370**(Lg\*≈0.0124 H),真鞍结(两 vcd 平衡合并:间距 459→16→0)。
- **与 PLL Hopf 的关系**:弱网先在 **SCR_H≈0.905** 撞 PLL 模 Hopf(失稳),更深到 SCR\*≈0.370 才撞
  鞍结。两机制都真实存在于 sweep.py,**PLL Hopf 先发生 = binding constraint**,真 R2 鞍结是二级机制。
- **数值验证**(`numerical/R2real_validate.py`,3 组参数):disc 符号精确对应真平衡数,残差 ~1e-11,
  且**与 sweep.py 自带 `pv()` 的 None 边界逐点吻合**。fold 随载荷物理移动(idr=120 → SCR\*=0.555)。

### 经典对照(scope = textbook 单摆,非 §12 GFL)—— `kyx/R2_fold.kyx`、`R2_sigma2_symbolic.kyx`

`Φ(p)=M²−Vg²`,`M=id_ref·wn·Lg+iq_ref·Rg`。数学正确,但这是**经典单轴摆 / Wu 边界**:它丢了真
fold 的 d 轴项与 LC 电容项(数值上 d 轴 Cterm≈300 比 M 还大,不可略)。`M` 本身可追溯(=真平衡的
q 轴量 K2),但 `|M|=Vg` 只是真 fold 在 Cterm=0 的退化特例。**保留作经典对照,不作 GFL 结论**;
真 GFL 的 fold 以上面 R2-real 为准。

## R3 — 同步吸引域 vs PLL 阻尼

- **⚠️ 模型审计(2026.06):** R3 的 swing 核 `δ'=dw, dw'=−b·dw−K·sinδ+Pm` **不在任何提交模型里**。
  §12/`sweep.py` 是 stiff-bus 电流控制 GFL,**无 swing 方程、无 H/D 惯量、无 sinδ 同步力矩**;
  §13/freq_mode 有 swing(`F9_S=κ·e_P−b·dw`,b=D/2H)但**无 sinδ、无角状态 δ**(§13.7 Thm C 才增广
  角态,且是线性 `−βKs·δ` 不是 `−K·sinδ`)。所以 R3 是**经典同步机摆方程(textbook pendulum)**,
  与 R2 同源(同一个经典摆),**不是仓库的 GFL**。证书数学正确,但 scope = 经典摆,非 §12/§13。
- **R3-pre(边界类型)**:(经典摆上)吸引域边界 = 鞍点稳定流形(数值 V_saddle=63 ≫ c*),
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

1. **dL/QE 不是线性代数/分析包**。证书证的是各机制**归约到的代数命题**(fold 不等式、
   能量恒等式、单调蕴含),不是完整符号谱或全局吸引域。
2. **R1 撤回**:见上,造模型错误,无成果。
3. **R3a 是约化同步核 + 内估**,不是 10D 全状态严格吸引域。
   - **10D 全非线性 SOS 没做到**:`SumOfSquares`/picos 装不上;手搭 cvxpy SOS 对同步核
     **infeasible**(查实因:误用的交叉项 V 根本不是 Lyapunov 函数,1424 处 Vdot>0,
     SOS 正确拒绝证伪)。改用能量法绕过,得到的是**约化核**的严格屏障。
   - 10D **线性** Lyapunov 盆需 balancing 预处理才解得动(裸 SCS 在 cond=2.2e5 下失败);
     这条没单独落成证书,仅记录于此。
4. **R3b 单调性**的证书证的是**符号代数蕴含**(逐点耗散 b₂>b₁⟹更大),其中数值数据
   来自数值扫描,是前提不是结论的一部分,已在证书注释标明。
5. 这些是**参数化失稳机制的代数骨架**,适合作工程稳定边界的形式化锚点;**不**等价于
   "已严格证明该 10D 系统在某区域全局稳定"。

## 关于 l₁(与 `numerical/` 的关系)

R3-note 用到的 l₁(第一 Lyapunov 系数)来自 `formalization/numerical/sweep.py` 的弱网
Hopf 管线(另一条线)。R3-note 的要点正是:**那条线的 l₁ 符号不能用来判全局失同步** —
这也是为什么本目录的 R3 改用 R2-fold + 能量屏障而非 Bautin/l₁ 框架。
