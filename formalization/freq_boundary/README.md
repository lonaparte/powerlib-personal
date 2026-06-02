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

### 能否符号化 / 形式化?(诚实)
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

### 诚实:完整形式化超出当前证明器
- F1(稳定极限环存在,|μ_F|<1)、F2(两环折叠合并,T 有界)需周期解 + 中心流形 + Floquet 理论,
  Mathlib/KeYmaera X **没有**这套库。**deductive 证不出**;现实可达是 validated numerics(interval
  continuation + 区间 Floquet,CAPD 思路)——本轮**未做**,明示为 open。

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
| F-fold F1/F2(极限环存在 + 折叠) | ❌ 超出证明器(需 Floquet/中心流形);validated-numerics 未做 |
| F-fold F3(无平衡 ⟹ 漂移 + 边界) | ✅ KeYmaera X proved(`ffold_f3_drift.kyx`,2) |

- F-H 是线性边界:**卡在 CAS 规模 + 不可低阶约化,不卡数学**;签名机制已证,真模型已核对。
- F-fold 是非线性全局边界:**真失同步充要条件**,完整形式化超出现状;可证子块 F3 已拿下。
- l₁/super-sub **不**作失同步判据(旁证,未入命题)。数值只核对,不进任何命题。

## 文件
- `fh_gate.py` — 对象闸门:任务 RHS 转录 + 谱 vs sweep.py(SCR_H 0.950 vs 0.905)。
- `fh_hurwitz.py` — Σ_H 的 Liénard–Chipart 签名 + H1/H2/H3 真模型验证。
- `fh_reduce.py` — 低阶约化测试(2D/4D 均**复现不出** Hopf 的负结果)。
- `kyx/fh_hopf_signature.kyx` — Hopf 签名机制(deg-2、deg-4 LC),3 条 proved。
- `kyx/ffold_f3_drift.kyx` — F-fold F3 代数子块,2 条 proved。

复现:`python3 fh_gate.py; python3 fh_hurwitz.py; python3 fh_reduce.py`;
`cd kyx && java -jar <keymaerax.jar> -prove <file>.kyx -tool z3`。
