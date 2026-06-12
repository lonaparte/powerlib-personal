# 风险机制的参数化证书(R2 已改对锚定真模型;R1 撤回;R3 标经典摆)

> **⚠️ 已迁移:** 通过标准化验证流程(对象闸门 → 参数化 → KeYmaera X → 数值核对)的 **R2real**
> 证书及其闸门/验证脚本(`R2real_fold.kyx`、`R2real_validate.py`、`R1_real_model_test.py`、
> `R2R3_model_audit.py`)已移至仓库根的 **`/02/risk_mechanisms/`**。本目录仅保留**经典摆对照**
> 证书(`R2_fold`、`R2_sigma2_symbolic`、`R3a`、`R3_basin`、`R3note`)——它们数学正确但卡在
> 对象闸门(非仓库 GFL),不计入"遵循流程"的成果。审计与流程见 `/02/README.md`。
>
> **2026.06 模型审计 + 改对(按 R1 同标准把 R1/R2/R3 全查了一遍,并把能改对的改对):**
>
> - **R1 — 撤回**:8×8 电气 A_e 是手编矩阵;且经真模型检验,弱网失稳是 PLL 模、无电气 onset。
>   见 `R1_RETRACTED.md` + `numerical/R1_real_model_test.py`。**机制不存在,无可改,永久撤回。**
> - **R2 — ✅ 已改对**:经典 `|M|=Vg` 不是真 fold。**已在真模型 sweep.py 上重做**:真失平衡是
>   vcd 平衡二次的**鞍结 disc=0**(系数全真),`kyx/R2real_fold.kyx`(5 条全 proved)+ 3 组数值验证
>   (`numerical/R2real_validate.py`,与 sweep.py 的 `pv()` 崩溃边界逐点吻合)。真 fold 在 SCR\*≈0.370,
>   比 PLL Hopf(SCR_H≈0.905)更深。旧经典 `|M|=Vg` 降为对照。
> - **R3 — 真版已存在,经典版降对照**:swing 核 `δ'=dw, dw'=−b·dw−K·sinδ+Pm` **不在任何提交模型里**
>   (§12 无 swing/惯量,§13 有 swing 但无 sinδ/角态)。真模型的"裕度 vs PLL 阻尼"已严格做对:
>   线性裕度 SCR_H(Kp) **U 型有最优**(Kp≈0.45),临界性在 **Bautin 点 Kp\*≈0.40 变号**(硬↔软),
>   严格 interval 版在 `numerical/bautin_cert/`(Kp\*∈[0.400,0.408]),bridge `numerical/R3real_check.py`。
>   经典摆 R3a/R3_basin/R3note 降为对照(且经典版说裕度单调,真模型是 U 型,形状都不同)。
>
> 真 GFL 的弱网**失稳**(非 fold)在 `numerical/`、`freq_mode/`、`bautin_cert/`(PLL 模 Hopf,
> SCR_H≈0.905,l₁ 符号/Bautin)。真 R2 鞍结(更深弱网,SCR≈0.370)在 `kyx/R2real_fold.kyx`。

## 状态总览(审计 + 改对后)

| 文件 | entry | KeYmaera X | scope |
|------|-------|-----------|------|
| `R1_RETRACTED.md` | — | **撤回** | 手编模型 + 真模型检验机制不存在 |
| `kyx/R2real_fold.kyx` | 5 | **proved** | ✅ **真模型** sweep.py 鞍结 fold disc=0(系数全真,3 组数值验证) |
| `kyx/R2_fold.kyx` | 4 | proved | 经典摆对照;\|M\|=Vg 非真 fold(降级) |
| `kyx/R2_sigma2_symbolic.kyx` | 2 | proved | 经典摆 Σ₂ 闭式(对照,scope=Wu 边界) |
| **R3 真版** → `numerical/bautin_cert/` | — | interval-sound | ✅ **真模型** §12 Hopf 临界性:Bautin Kp\*∈[0.400,0.408](硬↔软);裕度 U 型 |
| `kyx/R3a_energy_barrier.kyx` | 3 | proved | 经典摆能量屏障 Vdot=−b·dw²(对照,2D 核) |
| `kyx/R3_basin.kyx` | 4 | proved | 经典摆吸引域(对照);**注**真裕度 U 型非单调 |
| `kyx/R3note_decoupling.kyx` | 3 | proved | 经典摆 l₁ vs 鞍点裕度解耦(对照);真模型 l₁ 是硬/软判据 |
| **proved 合计** | **21** | | R2real(5,真模型)+ 经典摆对照(16);R3 真版在 bautin_cert(interval) |

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
- **10D 全状态 ROA 的严格证书(SOS)仍未做到**:全非线性 SOS 求解器装不上;手搭 SOS 对核
  infeasible(查实因是误用的交叉项 V 非 Lyapunov 函数)。**已做到的是数值内估**:`R3_roa.py`
  积分真 10D 非线性场,给出临界功率角 Δθ_crit(SCR) 这条暂态裕度(过了对象闸门)——这是真模型上
  的 ROA **数值切片**,不是保证内界(保证内界需 Lyapunov sublevel set,未做)。经典 R3a/R3_basin
  仍是 2D 约化核的对照。
- **R3-note 的"全局 LOS"严格化**:数值时域已做(`R3_roa.py` 显示 SCR→0.905⁺ 时 ROA→0、硬 Hopf
  在线性边界前塌缩);但**严格 dL/区间时域证书**未做。
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

## R3 — 同步裕度 vs PLL 阻尼

### ✅ R3-real(真模型答案,已存在且严格)—— `numerical/bautin_cert/` + `freq_mode/`

真模型(§12 10 状态 GFL)的弱网失稳是 **PLL 模 Hopf**,"裕度 vs PLL 阻尼"有两个真答案,均出自
已验证的 sweep.py 管线(bridge:`numerical/R3real_check.py`):

1. **线性裕度 SCR_H(Kp) 是 U 型(非单调)**:Kp 0.10→1.40 时 SCR_H 1.96→谷底 0.79(Kp≈0.45)→1.34,
   **有内部最优 PLL 增益**让弱网裕度最大。经典 R3b 说的"c*(ζ) 单调"形状就是错的——真裕度有最优点。
2. **临界性(硬/软)在 Bautin 点变号**:l₁ 沿 Hopf locus 在 **Kp\*≈0.40** 变号(subcritical/硬/危险
   ↔ supercritical/软)。**严格 interval-sound 版本已在 `numerical/bautin_cert/`**(区间 Kp\*∈[0.400,0.408],
   真 10 状态 §12 模型,Krawczyk/Rump 验证)。`R3real_check.py` 的 float Kp\*≈0.405 与之一致。

最优 PLL 增益(≈0.45)恰在 Bautin 点(≈0.40)附近——真模型的物理结论。

3. **非线性吸引域(暂态裕度)** `numerical/R3_roa.py`:**积分真 10D 非线性场**(非 Jacobian),
   先过对象闸门(`‖f(x_eq)‖~1e-11`、`‖Jac−Amat‖/‖Amat‖~1e-18`,确认积分的就是真模型),再测稳定
   平衡能恢复的**临界功率角 Δθ_crit**(暂态稳定/critical-clearing 类比):

   | SCR | 2.0 | 1.5 | 1.2 | 1.0 | 0.95 |
   |-----|-----|-----|-----|-----|------|
   | Δθ_crit | 148° | 136° | 100° | 44° | ~0 |

   ROA 随弱网**单调收缩**,在 Hopf(SCR_H≈0.905)处归零。SCR=0.95(仍线性稳)时已 tiny——正是 Kp=0.30
   **subcritical(硬)Hopf**(l₁>0,见 bautin_cert)的预言:稳定侧有不稳定极限环,基域在线性边界**之前**
   就塌缩。三条线(非线性 ROA、线性裕度 SCR_H、Bautin 临界性)互相印证。

**R3 的真版以 bautin_cert/(临界性,严格)+ freq_mode/(Hopf 结构,§13 17/17)+ R3_roa.py
(非线性暂态裕度,数值)为准。**

### 经典对照(scope = textbook 倾斜摆,非 §12/§13 GFL)—— `kyx/R3a_*`、`R3_basin.kyx`、`R3note_*`

swing 核 `δ'=dw, dw'=−b·dw−K·sinδ+Pm` **不在任何提交模型里**(§12 无 swing/惯量/sinδ;§13 有 swing
但无 sinδ/角态,§13.7 Thm C 增广的是线性 `−βKs·δ`)。与 R2 经典版同源(同一个摆)。下列证书数学正确
但 **scope 是经典摆**,降为对照:
- **R3a**:倾斜摆能量 `V=½dw²+K(cosδ*−cosδ)−Pm(δ−δ*)`,`Vdot=−b·dw²` 精确(误差 7e-17),
  LaSalle {V<c*} 内估。`R3a_energy_barrier.kyx`(3)。
- **R3b**:经典摆 c*(阻尼) 单调。`R3_basin.kyx`(4)。**注**:真模型裕度是 U 型,非单调——见上。
- **R3-note**:经典摆里 sign l₁ 非失同步判据(失同步由鞍点裕度管)。`R3note_decoupling.kyx`(3)。
  **注**:此结论是关于经典摆的"鞍结失同步";真模型的主失稳是 Hopf,那里 l₁ 符号恰恰**是**硬/软
  判据(Bautin,见 bautin_cert/)——两者是不同机制,不矛盾,但 R3note 答的是错模型的问题。

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
