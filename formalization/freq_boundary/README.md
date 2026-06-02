# F-H / F-fold — GFL-VSC 弱网失同步的两条参数化边界

> 按给定任务规格(converter-frame 10 状态模型)做 **F-H**(Hopf 起振面 Σ_H,线性/代数)
> 与 **F-fold**(极限环鞍结面 Σ_fold,非线性/全局)。诚实分层:能证的证(KeYmaera X),
> 能在真模型上核对的核对(数值,不进命题),证不动的明说。

## 0. 对象闸门(先核对模型,R1 教训)

- 任务说模型 = `run_sde_schafer.full_dynamics_ad`,**该文件不在本仓库**。权威取 (a) 任务里写出的
  显式 RHS,(b) 已验证的 `sweep.py`(§12)。
- 任务 RHS 是 **converter-frame**(c=cosθ_e, s=sinθ_e, PLL 反馈 `v_cqc=s·v_cd+c·v_cq`),与 §13
  `freq_mode` 的帧一致,**不是** `sweep.py`(§12,grid-frame,PLL 反馈 `v_cq`)的写法。
- **谱不一致**(`fh_gate.py`,残差 ~1e-10):任务模型 Hopf 在 **SCR_H≈0.950**,`sweep.py` 在 **0.905**。
  二者是**不同(相近)模型**(PLL 反馈信号不同),非同一系统换帧。**故本目录对任务 RHS 本身做 F-H,
  不替换成 sweep.py**,并标明此差异。

## 1. F-H —— Hopf 起振面 Σ_H(线性,代数)

`χ(s;p)=det(sI−J)=s^10+a1 s^9+…+a10`;`Σ_H := {Δ_9=0, Δ_{1..8}>0, a10>0}`(Liénard–Chipart)。

### 真模型上验证(数值,`fh_hurwitz.py`;数值只核对)
- **(H1)** J Hurwitz ⟺ 全 Δ_k>0:稳定侧(SCR>0.950)全正,越过后失效。✓
- **Σ_H 签名**:Δ_9 在 SCR_H≈0.950 处 **+→− 变号**,Δ_{1..8}>0、a10>0 全程保持。✓
- **(H2)** 恰一对共轭在虚轴 **±238.7j**;偶部 `E(W)=0`(W=ω²)正根 √W=**238.689 rad/s**(38 Hz)
  与临界特征值 |Im λ| 逐位吻合。✓
- **(H3)** 横截性 `dReλ/dg>0`(g=1/Lg,弱网→RHP),且 Δ_9 跨 Σ_H 由 + 变 −。✓

### ✅ 子空间显式 Σ_H(已做到,`fh_sigmaH_pll.py`)
PLL 增益子空间 (Kp_pll, Ki_pll) 上 Σ_H **能写成显式关系**,因为两个结构事实(已验证,非假设):
- **(S1)** 平衡 x\* **不依赖** PLL 增益(平衡处 v_cqc=0,η=0;数值核对 ‖Δx*‖=1.4e-16)。
- **(S2)** 增益只进 J 的 θ_e' **一行、线性** ⟹ det(sI−J) 对 (Kp,Ki) **仿射** ⟹ 每个 `a_k=α_k+β_k·Kp+γ_k·Ki`
  **精确**(行列式对单行多线性;相对误差 1.6e-13)。故 **Δ_9(Kp,Ki) 是显式 ≤9 次多项式**,
  其数据就是 11 组 (α_k,β_k,γ_k)(脚本打印)。
- **Σ_H={Δ_9=0} 边界曲线 + sign chart**:在固定网(SCR=0.95)上,边界 Kp\*(Ki) 经直接特征值 Hopf
  **逐点核对**(曲线上 maxRe~1e-11),过名义 Hopf (0.30,150)(Kp\*=0.30005)。**稳定侧 Kp>Kp\***
  (比例增益越大越稳),Kp\* 随 Ki 上升(0.175→0.300→0.473)。这就是你要的"子空间符号 Σ_H + 穿越方向"。
- 全 Δ_9 展开仍 CAS 爆(系数 1→1e27);但**不需要**——仿射数据已把边界确定到任意精度。

### 全 10D 能否符号化 / 形式化?(诚实)
- **全 10×10 符号 Δ_9(p):CAS 爆。** 而且**不可低阶约化**(`fh_reduce.py`:把 8 个快电气态按准稳态
  Schur 消去得 2×2、或保留 PLL+网侧电流的 4×4,**都复现不出 Hopf**——tr 恒 ≪0 / Hopf 跑到 0.90)。
  即 38 Hz 模是**真高维模**,无干净低阶特征多项式。故无 10D 参数化 Σ_H 的 dL 证书。
- **可证的核(`kyx/fh_hopf_signature.kyx`,3 条 proved)**:Hopf 签名**机制**在 QE 可处理的阶上证清——
  **degree-4 Liénard–Chipart**:`Δ_3=0 ∧ a1,a3,a4>0 ⟹` 取 `ω²=a3/a1` 时偶部 `a1²(W²−a2W+a4)=−Δ_3=0`、
  奇部 `a3−a1W=0` 同时为零 ⟹ 纯虚对(且 ω²>0)。这与模型 Σ_H 的 `Δ_9=0` **同构**,只差阶数。
  degree-2 基础条件(tr=0∧det>0)同证。数值交叉验证 5 组随机 4 次多项式,Re~机器零 @ ω=√(a3/a1)。
- **(可选)l₁ 旁证**:按规格**不**作失同步判据,未纳入命题。真模型 l₁/Bautin 在 `../numerical/bautin_cert/`。

## 2. F-fold —— 极限环鞍结面 Σ_fold(非线性,全局)

**真正的失同步充要边界**,过 Σ_H 后稳定/不稳定极限环互相靠近、在 μ_F=+1 合并消失。

### ✅ F1(稳定极限环存在,过 Σ_H)—— 两档已做(`ffold_cycle.py` + `ffold_l1_anchor.py`)
真模型(Kp_pll=0.50,该处 Hopf **超临界**)上,过 Σ_H 确有轨道稳定极限环,两个独立证据:
- **临界性锚(小幅严格根据)**:Hopf 第一 Lyapunov 系数 **l₁=−2.09e-6<0**(Kuznetsov 投影,
  解析 Jacobian 的 FD 张量;**符号对 FD 步长稳健**:h=2e-3/1e-3/5e-4 均 −2.09e-6)。l₁<0 ⟹ 超临界 ⟹
  **由 Hopf 分岔定理,Σ_H 刚过处存在小幅轨道稳定极限环**。这是 F1 小幅端的严格根据。
- **有限幅数值(Floquet)**:在 SCR=0.7866(过 Σ_H,SCR_H=0.7966)定位周期轨(Poincaré 截面,
  T=23.4 ms=42.7 Hz),算单值矩阵的 **Floquet 乘子**:平凡乘子≈1.0002(流向),**最大非平凡 |μ|=0.881<1**,
  其余快模 ≈0 ⟹ **轨道稳定**。F1 在有限幅端成立(数值)。

### ✅ F2(环折叠 Σ_fold)—— 参数化形式化(法形提升;`kyx/ffold_cyclefold_normalform.kyx`,5 条 proved)
把 F2 抬到 **Hopf 法形**:环折叠 = 幅值方程 `g(ρ)=l₂ρ²+l₁ρ+μ=0`(ρ=r²)的**二次鞍结**,与
`R2real_fold.kyx`(判别式 fold)**结构完全相同**,因而可参数化 QE 证:
- **折叠**:disc=l₁²−4l₂μ=0 时 ρ\*=−l₁/(2l₂) 是重根(两环合并);
- **折叠下方**:disc>0 两条不同极限环(稳+不稳,正是要合并的一对);
- **折叠上方**:l₂>0∧disc<0 ⟹ g>0 处处 ⟹ 无极限环(振荡支消失);
- **物理性**:ρ\*>0 ⟺ l₁·l₂<0(经典 sub/super + Bautin 配置);
- **Bautin 组织中心**:l₁=0 处折叠面与 Σ_H 相交(Σ_fold 从 Bautin 点发出,切于 Σ_H)。

**对象闸门**(`ffold_normalform.py`,确认任务模型真服从此法形,非假设):(A) 幅值² 对 μ-代理
线性 `ρ=19.3·δ−0.012`(小截距 ⟹ 法形成立);(B) 任务模型 **Bautin 点 Kp\*≈0.43**(l₁ 在 Kp=0.40→0.45
变号:+4.6e-7→−9.8e-7),Σ_fold 由此发出。

### ✅ F2 非退化 + 实际折叠定位(`ffold_l2_branch.py` + `ffold_locate.py`)—— 本轮补上
- **l₂≠0(Bautin 非退化)已算**:从极限环分支曲率拟合 `μ=−l₁ρ−l₂ρ²`(只用有界环点,滤掉逃逸):
  Kp=0.50 得 **l₂=+34.2**(l₁=−28.3,resid 2e-3),Kp=0.55 得 **l₂=+35.8**——**l₂>0 非退化**。
  l₂ 的**符号对幅值变量线性缩放不变**(`l₂→l₂/α⁴`),故符号(=非退化)是良定义的(|l₂| 同 |l₁| 是约定量)。
  **这补上了 bautin_cert 留的 Bautin 非退化缺口**(数值层;严格 5 阶法形 l₂ 区间仍是更重的一步)。
- **实际环折叠 Σ_fold 已定位**:Kp=0.50 扫 SCR,稳定环到 SCR=0.7866(μ=4.24)仍在,到 SCR=0.7766
  (μ=8.53)**逃逸(θ_e 漂移 ~9000 = 失同步)**。⟹ Σ_fold 在 μ∈[4.24,8.53]。
- **交叉验证**:小幅法形拟合预测的折叠 **μ_fold=l₁²/4l₂=5.86 恰落在实测逃逸窗 [4.24,8.53] 内**。
  即:已证的法形折叠结构 + 数值系数 → 预测折叠位置,直接积分确认 → **F2 在任务模型上兑现且自洽**。

### 诚实:仍未做到(明示)
- **interval-sound 的 l₁<0 / l₂(把数值升到计算机辅助证明档)**:bautin_cert 那套
  (Krawczyk 特征对 + 区间张量)在 sweep.py 上成立,但**搬到任务模型受阻于其平衡点无闭式**
  (§12/sweep.py 有 vcd 二次闭式,任务模型平衡是超越方程、数值解),需额外**区间 Newton 包平衡点**一层。
  现 l₁<0、l₂>0 由**两条独立数值方法**(Kuznetsov 投影 + 分支曲率)一致确立,符号稳健,但非区间证。
- **F2 折叠面映回全 (Kp,SCR) 物理平面**:单点已定位(Kp=0.50: μ_fold≈5.86);整条 Σ_fold 曲线需沿
  分支 validated continuation,**未做**。
- 周期轨未 Newton 精化(闭合 ≈3.3e-3);**最大非平凡 |μ|=0.881 对此稳健**,结论不变。

### 可证子块 F3(代数,R2/Σ₂ 同型;`kyx/ffold_f3_drift.kyx`,2 条 proved)
- **F3a**:角平衡 `θ' = M − Vg·sin θ`,过 fold 后 `|M|>Vg`(用 `s²≤1` 编码 sin)⟹ `M−Vg·s>0` 处处成立
  ⟹ 角速度定号、无零点(无平衡)⟹ θ 单调无界漂移 = 失同步。
- **F3b**:互补的边界刻画——同步角平衡(`M=Vg·s, s²≤1`)存在 ⟺ `M²≤Vg²`。这是角层 Σ_fold|_angle 折叠,
  与 `../risk_mechanisms/kyx/R2_fold.kyx`、`R2real_fold.kyx`(真模型鞍结 disc=0)同族。

## 3. 诚实分层(对应任务规格)

| 命题 | 状态 |
|------|------|
| F-H Σ_H 签名 + H1/H2/H3(任务真模型) | ✅ 数值核对(`fh_hurwitz.py`),SCR_H≈0.950, ω_H=38 Hz |
| F-H 低阶约化是否存在 | ❌ 否(`fh_reduce.py`,高维模)——故无低阶符号 Σ_H |
| F-H Hopf 签名机制(degree-4 LC) | ✅ KeYmaera X proved(`fh_hopf_signature.kyx`,3) |
| F-H 全 10D 符号 Δ_9(p) | ❌ CAS 爆 + 不可约化(明示) |
| F-fold F1(稳定极限环存在)小幅端 | ✅ l₁=−2.09e-6<0 超临界 + Hopf 定理(`ffold_l1_anchor.py`);l₁ 区间化未做 |
| F-fold F1 有限幅(Floquet \|μ\|<1) | ✅ 数值:max 非平凡 \|μ\|=0.881<1(`ffold_cycle.py`) |
| F-fold F2 折叠**结构**(法形鞍结) | ✅ KeYmaera X proved(`ffold_cyclefold_normalform.kyx`,5;R2 同型);法形成立+Bautin Kp*≈0.43 已核对 |
| F-fold F2 非退化 l₂≠0(Bautin) | ✅ 数值:l₂=+34.2(Kp=.50)/+35.8(Kp=.55),符号不变量(`ffold_l2_branch.py`);区间 l₂ 未做 |
| F-fold F2 实际折叠定位 + 失同步 | ✅ 数值:Σ_fold μ∈[4.24,8.53],预测 μ_fold=5.86 落其中;过后 θ_e 漂移~9000(`ffold_locate.py`) |
| F-fold F2 整条 Σ_fold(全 Kp,SCR) | ❌ 需沿分支 validated continuation;单点已定位,整条未做 |
| F-fold F3(无平衡 ⟹ 漂移 + 边界) | ✅ KeYmaera X proved(`ffold_f3_drift.kyx`,2) |

- F-H 是线性边界:**卡在 CAS 规模 + 不可低阶约化,不卡数学**;签名机制已证,真模型已核对。
- F-fold 是非线性全局边界:**真失同步充要条件**。F1(稳定极限环存在)已做(l₁<0 超临界锚 +
  Floquet \|μ\|=0.881<1);F3 代数子块 KeYmaera X 已证;F2(环折叠)与 l₁ 区间化仍 open。
- l₁/super-sub **不**作失同步判据(旁证,未入命题)。数值只核对,不进任何命题。

## 文件
- `fh_gate.py` — 对象闸门:任务 RHS 转录 + 谱 vs sweep.py(SCR_H 0.950 vs 0.905)。
- `fh_hurwitz.py` — Σ_H 的 Liénard–Chipart 签名 + H1/H2/H3 真模型验证。
- `fh_reduce.py` — 低阶约化测试(2D/4D 均**复现不出** Hopf 的负结果)。
- `kyx/fh_hopf_signature.kyx` — Hopf 签名机制(deg-2、deg-4 LC),3 条 proved。
- `fh_sigmaH_pll.py` — 子空间显式 Σ_H(Kp_pll, Ki_pll):仿射系数 + 边界曲线 + sign chart。
- `fh_model_sym.py` — 任务 RHS 的 SymPy 版 + 解析 Jacobian(lambdify,供积分加速)。
- `ffold_cycle.py` — F1 有限幅:Poincaré 定轨 + Floquet 乘子(max 非平凡 \|μ\|=0.881<1)。
- `ffold_l1_anchor.py` — F1 小幅锚:Hopf 第一 Lyapunov 系数 l₁=−2.09e-6<0(超临界)。
- `ffold_normalform.py` — F2 对象闸门:法形成立(幅值²~μ 线性)+ Bautin 点 Kp*≈0.43。
- `ffold_l2_branch.py` — F2 非退化:分支曲率拟合 l₂>0(Bautin 非退化,补 bautin_cert 缺口)。
- `ffold_locate.py` — F2 实际折叠:Σ_fold 定位(μ_fold≈5.86)+ 过后失同步(θ_e 漂移)。
- `kyx/fh_hopf_signature.kyx` — Hopf 签名机制(deg-2、deg-4 LC),3 条 proved。
- `kyx/ffold_cyclefold_normalform.kyx` — F2 环折叠法形鞍结(R2 同型),5 条 proved。
- `kyx/ffold_f3_drift.kyx` — F-fold F3 代数子块,2 条 proved。

复现:`python3 fh_gate.py; python3 fh_hurwitz.py; python3 fh_reduce.py`;
`cd kyx && java -jar <keymaerax.jar> -prove <file>.kyx -tool z3`。
